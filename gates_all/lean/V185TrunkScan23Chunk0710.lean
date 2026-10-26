import V185TrunkScan23Chunk0709

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4196698 : List Nat := [3, 1, 1, 2, 1, 2, 1, 5, 2, 5]
def baseStart_4196698 : Nat := 118140960795 + 4196698 * 2 ^ 59
def prefixEnd_4196698 : Nat := 4983230072969 + 3 ^ 40 * 4196698 * 2
def baseEnd_4196698 : Nat := 718307745254175544491581

theorem tailTrace_4196698 : CollatzResearch.WordTrace tailWord_4196698 prefixEnd_4196698 718307745254175544491581 := by
  unfold tailWord_4196698
  simp only [CollatzResearch.WordTrace]
  refine ⟨38266537737521839950251687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102044100633391573200671165 38266537737521839950251687)
  ·
    refine ⟨57399806606282759925377531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38266537737521839950251687 57399806606282759925377531)
    ·
      refine ⟨86099709909424139888066297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57399806606282759925377531 86099709909424139888066297)
      ·
        refine ⟨64574782432068104916049723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86099709909424139888066297 64574782432068104916049723)
        ·
          refine ⟨96862173648102157374074585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64574782432068104916049723 96862173648102157374074585)
          ·
            refine ⟨72646630236076618030555939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96862173648102157374074585 72646630236076618030555939)
            ·
              refine ⟨108969945354114927045833909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72646630236076618030555939 108969945354114927045833909)
              ·
                refine ⟨10215932376948274410546929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108969945354114927045833909 10215932376948274410546929)
                ·
                  refine ⟨7661949282711205807910197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10215932376948274410546929 7661949282711205807910197)
                  ·
                    refine ⟨718307745254175544491581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7661949282711205807910197 718307745254175544491581)
                    ·
                      rfl

theorem cell23_4196698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 2, 5].length) (baseStart_4196698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196698 prefixEnd_4196698 := by exact prefixLift 4196698
  have htrace : WordTrace (prefixWord ++ tailWord_4196698) baseStart_4196698 baseEnd_4196698 := by
    simpa [prefixWord, tailWord_4196698, baseEnd_4196698] using wordTrace_append hprefix tailTrace_4196698
  have hstable : (prefixWord ++ tailWord_4196698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196698).length < 2 ^ (prefixWord ++ tailWord_4196698).sum := by decide
  have hdescent : baseEnd_4196698 < baseStart_4196698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196708 : List Nat := [2, 3, 1, 1, 3, 1, 2, 2, 1, 2, 5]
def baseStart_4196708 : Nat := 118140960795 + 4196708 * 2 ^ 59
def prefixEnd_4196708 : Nat := 4983230072969 + 3 ^ 40 * 4196708 * 2
def baseEnd_4196708 : Nat := 2154928370569071594349697

theorem tailTrace_4196708 : CollatzResearch.WordTrace tailWord_4196708 prefixEnd_4196708 2154928370569071594349697 := by
  unfold tailWord_4196708
  simp only [CollatzResearch.WordTrace]
  refine ⟨76533257840025565754435389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102044343786700754339247185 76533257840025565754435389)
  ·
    refine ⟨28699971690009587157913271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76533257840025565754435389 28699971690009587157913271)
    ·
      refine ⟨43049957535014380736869907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28699971690009587157913271 43049957535014380736869907)
      ·
        refine ⟨64574936302521571105304861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43049957535014380736869907 64574936302521571105304861)
        ·
          refine ⟨24215601113445589164489323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64574936302521571105304861 24215601113445589164489323)
          ·
            refine ⟨36323401670168383746733985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24215601113445589164489323 36323401670168383746733985)
            ·
              refine ⟨27242551252626287810050489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36323401670168383746733985 27242551252626287810050489)
              ·
                refine ⟨20431913439469715857537867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27242551252626287810050489 20431913439469715857537867)
                ·
                  refine ⟨30647870159204573786306801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20431913439469715857537867 30647870159204573786306801)
                  ·
                    refine ⟨22985902619403430339730101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30647870159204573786306801 22985902619403430339730101)
                    ·
                      refine ⟨2154928370569071594349697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22985902619403430339730101 2154928370569071594349697)
                      ·
                        rfl

theorem cell23_4196708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_4196708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196708 prefixEnd_4196708 := by exact prefixLift 4196708
  have htrace : WordTrace (prefixWord ++ tailWord_4196708) baseStart_4196708 baseEnd_4196708 := by
    simpa [prefixWord, tailWord_4196708, baseEnd_4196708] using wordTrace_append hprefix tailTrace_4196708
  have hstable : (prefixWord ++ tailWord_4196708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196708).length < 2 ^ (prefixWord ++ tailWord_4196708).sum := by decide
  have hdescent : baseEnd_4196708 < baseStart_4196708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196725 : List Nat := [1, 3, 4, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_4196725 : Nat := 118140960795 + 4196725 * 2 ^ 59
def prefixEnd_4196725 : Nat := 4983230072969 + 3 ^ 40 * 4196725 * 2
def baseEnd_4196725 : Nat := 2154937099740198027837119

theorem tailTrace_4196725 : CollatzResearch.WordTrace tailWord_4196725 prefixEnd_4196725 2154937099740198027837119 := by
  unfold tailWord_4196725
  simp only [CollatzResearch.WordTrace]
  refine ⟨153067135720989543412239629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102044757147326362274826419 153067135720989543412239629)
  ·
    refine ⟨57400175895371078779589861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153067135720989543412239629 57400175895371078779589861)
    ·
      refine ⟨10762532980382077271173099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57400175895371078779589861 10762532980382077271173099)
      ·
        refine ⟨16143799470573115906759649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10762532980382077271173099 16143799470573115906759649)
        ·
          refine ⟨12107849602929836930069737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16143799470573115906759649 12107849602929836930069737)
          ·
            refine ⟨9080887202197377697552303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12107849602929836930069737 9080887202197377697552303)
            ·
              refine ⟨13621330803296066546328455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9080887202197377697552303 13621330803296066546328455)
              ·
                refine ⟨20431996204944099819492683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13621330803296066546328455 20431996204944099819492683)
                ·
                  refine ⟨30647994307416149729239025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20431996204944099819492683 30647994307416149729239025)
                  ·
                    refine ⟨22985995730562112296929269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30647994307416149729239025 22985995730562112296929269)
                    ·
                      refine ⟨2154937099740198027837119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22985995730562112296929269 2154937099740198027837119)
                      ·
                        rfl

theorem cell23_4196725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_4196725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196725 prefixEnd_4196725 := by exact prefixLift 4196725
  have htrace : WordTrace (prefixWord ++ tailWord_4196725) baseStart_4196725 baseEnd_4196725 := by
    simpa [prefixWord, tailWord_4196725, baseEnd_4196725] using wordTrace_append hprefix tailTrace_4196725
  have hstable : (prefixWord ++ tailWord_4196725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196725).length < 2 ^ (prefixWord ++ tailWord_4196725).sum := by decide
  have hdescent : baseEnd_4196725 < baseStart_4196725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196775 : List Nat := [1, 1, 6, 1, 1, 2, 1, 4, 6]
def baseStart_4196775 : Nat := 118140960795 + 4196775 * 2 ^ 59
def prefixEnd_4196775 : Nat := 4983230072969 + 3 ^ 40 * 4196775 * 2
def baseEnd_4196775 : Nat := 239440308196991425801321

theorem tailTrace_4196775 : CollatzResearch.WordTrace tailWord_4196775 prefixEnd_4196775 239440308196991425801321 := by
  unfold tailWord_4196775
  simp only [CollatzResearch.WordTrace]
  refine ⟨153068959370808401951559779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102045972913872267967706519 153068959370808401951559779)
  ·
    refine ⟨229603439056212602927339669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153068959370808401951559779 229603439056212602927339669)
    ·
      refine ⟨10762661205759965762219047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 229603439056212602927339669 10762661205759965762219047)
      ·
        refine ⟨16143991808639948643328571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10762661205759965762219047 16143991808639948643328571)
        ·
          refine ⟨24215987712959922964992857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16143991808639948643328571 24215987712959922964992857)
          ·
            refine ⟨18161990784719942223744643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24215987712959922964992857 18161990784719942223744643)
            ·
              refine ⟨27242986177079913335616965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18161990784719942223744643 27242986177079913335616965)
              ·
                refine ⟨5108059908202483750428181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27242986177079913335616965 5108059908202483750428181)
                ·
                  refine ⟨239440308196991425801321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5108059908202483750428181 239440308196991425801321)
                  ·
                    rfl

theorem cell23_4196775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 6].length) (baseStart_4196775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196775 prefixEnd_4196775 := by exact prefixLift 4196775
  have htrace : WordTrace (prefixWord ++ tailWord_4196775) baseStart_4196775 baseEnd_4196775 := by
    simpa [prefixWord, tailWord_4196775, baseEnd_4196775] using wordTrace_append hprefix tailTrace_4196775
  have hstable : (prefixWord ++ tailWord_4196775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196775).length < 2 ^ (prefixWord ++ tailWord_4196775).sum := by decide
  have hdescent : baseEnd_4196775 < baseStart_4196775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196848 : List Nat := [2, 1, 1, 1, 3, 3, 2, 10]
def baseStart_4196848 : Nat := 118140960795 + 4196848 * 2 ^ 59
def prefixEnd_4196848 : Nat := 4983230072969 + 3 ^ 40 * 4196848 * 2
def baseEnd_4196848 : Nat := 79814824365211149874039

theorem tailTrace_4196848 : CollatzResearch.WordTrace tailWord_4196848 prefixEnd_4196848 79814824365211149874039 := by
  unfold tailWord_4196848
  simp only [CollatzResearch.WordTrace]
  refine ⟨76535810949771967709483599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102047747933029290279311465 76535810949771967709483599)
  ·
    refine ⟨114803716424657951564225399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76535810949771967709483599 114803716424657951564225399)
    ·
      refine ⟨172205574636986927346338099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114803716424657951564225399 172205574636986927346338099)
      ·
        refine ⟨258308361955480391019507149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172205574636986927346338099 258308361955480391019507149)
        ·
          refine ⟨96865635733305146632315181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 258308361955480391019507149 96865635733305146632315181)
          ·
            refine ⟨36324613399989429987118193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96865635733305146632315181 36324613399989429987118193)
            ·
              refine ⟨27243460049992072490338645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36324613399989429987118193 27243460049992072490338645)
              ·
                refine ⟨79814824365211149874039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 27243460049992072490338645 79814824365211149874039)
                ·
                  rfl

theorem cell23_4196848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 10].length) (baseStart_4196848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196848 prefixEnd_4196848 := by exact prefixLift 4196848
  have htrace : WordTrace (prefixWord ++ tailWord_4196848) baseStart_4196848 baseEnd_4196848 := by
    simpa [prefixWord, tailWord_4196848, baseEnd_4196848] using wordTrace_append hprefix tailTrace_4196848
  have hstable : (prefixWord ++ tailWord_4196848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196848).length < 2 ^ (prefixWord ++ tailWord_4196848).sum := by decide
  have hdescent : baseEnd_4196848 < baseStart_4196848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196865 : List Nat := [1, 2, 4, 1, 3, 2, 1, 9]
def baseStart_4196865 : Nat := 118140960795 + 4196865 * 2 ^ 59
def prefixEnd_4196865 : Nat := 4983230072969 + 3 ^ 40 * 4196865 * 2
def baseEnd_4196865 : Nat := 79815147667845462225425

theorem tailTrace_4196865 : CollatzResearch.WordTrace tailWord_4196865 prefixEnd_4196865 79815147667845462225425 := by
  unfold tailWord_4196865
  simp only [CollatzResearch.WordTrace]
  refine ⟨153072241940482347322336049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102048161293654898214890699 153072241940482347322336049)
  ·
    refine ⟨114804181455361760491752037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153072241940482347322336049 114804181455361760491752037)
    ·
      refine ⟨21525784022880330092203507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114804181455361760491752037 21525784022880330092203507)
      ·
        refine ⟨32288676034320495138305261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21525784022880330092203507 32288676034320495138305261)
        ·
          refine ⟨12108253512870185676864473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32288676034320495138305261 12108253512870185676864473)
          ·
            refine ⟨9081190134652639257648355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12108253512870185676864473 9081190134652639257648355)
            ·
              refine ⟨13621785201978958886472533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9081190134652639257648355 13621785201978958886472533)
              ·
                refine ⟨79815147667845462225425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13621785201978958886472533 79815147667845462225425)
                ·
                  rfl

theorem cell23_4196865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 9].length) (baseStart_4196865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196865 prefixEnd_4196865 := by exact prefixLift 4196865
  have htrace : WordTrace (prefixWord ++ tailWord_4196865) baseStart_4196865 baseEnd_4196865 := by
    simpa [prefixWord, tailWord_4196865, baseEnd_4196865] using wordTrace_append hprefix tailTrace_4196865
  have hstable : (prefixWord ++ tailWord_4196865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196865).length < 2 ^ (prefixWord ++ tailWord_4196865).sum := by decide
  have hdescent : baseEnd_4196865 < baseStart_4196865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196926 : List Nat := [4, 2, 1, 4, 1, 1, 1, 2, 1, 3, 3]
def baseStart_4196926 : Nat := 118140960795 + 4196926 * 2 ^ 59
def prefixEnd_4196926 : Nat := 4983230072969 + 3 ^ 40 * 4196926 * 2
def baseEnd_4196926 : Nat := 2155040309351751741423695

theorem tailTrace_4196926 : CollatzResearch.WordTrace tailWord_4196926 prefixEnd_4196926 2155040309351751741423695 := by
  unfold tailWord_4196926
  simp only [CollatzResearch.WordTrace]
  refine ⟨19134308349157669342538329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102049644528840903160204421 19134308349157669342538329)
  ·
    refine ⟨14350731261868252006903747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19134308349157669342538329 14350731261868252006903747)
    ·
      refine ⟨21526096892802378010355621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14350731261868252006903747 21526096892802378010355621)
      ·
        refine ⟨4036143167400445876941679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21526096892802378010355621 4036143167400445876941679)
        ·
          refine ⟨6054214751100668815412519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4036143167400445876941679 6054214751100668815412519)
          ·
            refine ⟨9081322126651003223118779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6054214751100668815412519 9081322126651003223118779)
            ·
              refine ⟨13621983189976504834678169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9081322126651003223118779 13621983189976504834678169)
              ·
                refine ⟨10216487392482378626008627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13621983189976504834678169 10216487392482378626008627)
                ·
                  refine ⟨15324731088723567939012941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10216487392482378626008627 15324731088723567939012941)
                  ·
                    refine ⟨5746774158271337977129853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15324731088723567939012941 5746774158271337977129853)
                    ·
                      refine ⟨2155040309351751741423695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5746774158271337977129853 2155040309351751741423695)
                      ·
                        rfl

theorem cell23_4196926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_4196926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196926 prefixEnd_4196926 := by exact prefixLift 4196926
  have htrace : WordTrace (prefixWord ++ tailWord_4196926) baseStart_4196926 baseEnd_4196926 := by
    simpa [prefixWord, tailWord_4196926, baseEnd_4196926] using wordTrace_append hprefix tailTrace_4196926
  have hstable : (prefixWord ++ tailWord_4196926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196926).length < 2 ^ (prefixWord ++ tailWord_4196926).sum := by decide
  have hdescent : baseEnd_4196926 < baseStart_4196926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196949 : List Nat := [1, 3, 2, 2, 1, 1, 2, 3, 4, 2, 2]
def baseStart_4196949 : Nat := 118140960795 + 4196949 * 2 ^ 59
def prefixEnd_4196949 : Nat := 4983230072969 + 3 ^ 40 * 4196949 * 2
def baseEnd_4196949 : Nat := 2155052119406805151436089

theorem tailTrace_4196949 : CollatzResearch.WordTrace tailWord_4196949 prefixEnd_4196949 2155052119406805151436089 := by
  unfold tailWord_4196949
  simp only [CollatzResearch.WordTrace]
  refine ⟨153075305672178029668393901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102050203781452019778929267 153075305672178029668393901)
  ·
    refine ⟨57403239627066761125647713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153075305672178029668393901 57403239627066761125647713)
    ·
      refine ⟨43052429720300070844235785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57403239627066761125647713 43052429720300070844235785)
      ·
        refine ⟨32289322290225053133176839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43052429720300070844235785 32289322290225053133176839)
        ·
          refine ⟨48433983435337579699765259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32289322290225053133176839 48433983435337579699765259)
          ·
            refine ⟨72650975153006369549647889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48433983435337579699765259 72650975153006369549647889)
            ·
              refine ⟨54488231364754777162235917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72650975153006369549647889 54488231364754777162235917)
              ·
                refine ⟨20433086761783041435838469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54488231364754777162235917 20433086761783041435838469)
                ·
                  refine ⟨3831203767834320269219713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20433086761783041435838469 3831203767834320269219713)
                  ·
                    refine ⟨2873402825875740201914785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3831203767834320269219713 2873402825875740201914785)
                    ·
                      refine ⟨2155052119406805151436089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2873402825875740201914785 2155052119406805151436089)
                      ·
                        rfl

theorem cell23_4196949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_4196949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196949 prefixEnd_4196949 := by exact prefixLift 4196949
  have htrace : WordTrace (prefixWord ++ tailWord_4196949) baseStart_4196949 baseEnd_4196949 := by
    simpa [prefixWord, tailWord_4196949, baseEnd_4196949] using wordTrace_append hprefix tailTrace_4196949
  have hstable : (prefixWord ++ tailWord_4196949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196949).length < 2 ^ (prefixWord ++ tailWord_4196949).sum := by decide
  have hdescent : baseEnd_4196949 < baseStart_4196949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196994 : List Nat := [3, 4, 3, 1, 2, 1, 1, 2, 2, 1, 3]
def baseStart_4196994 : Nat := 118140960795 + 4196994 * 2 ^ 59
def prefixEnd_4196994 : Nat := 4983230072969 + 3 ^ 40 * 4196994 * 2
def baseEnd_4196994 : Nat := 2155075226036257475373383

theorem tailTrace_4196994 : CollatzResearch.WordTrace tailWord_4196994 prefixEnd_4196994 2155075226036257475373383 := by
  unfold tailWord_4196994
  simp only [CollatzResearch.WordTrace]
  refine ⟨38269236739253750588445509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102051297971343334902521357 38269236739253750588445509)
  ·
    refine ⟨7175481888610078235333533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38269236739253750588445509 7175481888610078235333533)
    ·
      refine ⟨2690805708228779338250075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7175481888610078235333533 2690805708228779338250075)
      ·
        refine ⟨4036208562343169007375113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2690805708228779338250075 4036208562343169007375113)
        ·
          refine ⟨3027156421757376755531335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4036208562343169007375113 3027156421757376755531335)
          ·
            refine ⟨4540734632636065133297003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3027156421757376755531335 4540734632636065133297003)
            ·
              refine ⟨6811101948954097699945505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4540734632636065133297003 6811101948954097699945505)
              ·
                refine ⟨5108326461715573274959129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6811101948954097699945505 5108326461715573274959129)
                ·
                  refine ⟨3831244846286679956219347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5108326461715573274959129 3831244846286679956219347)
                  ·
                    refine ⟨5746867269430019934329021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3831244846286679956219347 5746867269430019934329021)
                    ·
                      refine ⟨2155075226036257475373383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5746867269430019934329021 2155075226036257475373383)
                      ·
                        rfl

theorem cell23_4196994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_4196994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196994 prefixEnd_4196994 := by exact prefixLift 4196994
  have htrace : WordTrace (prefixWord ++ tailWord_4196994) baseStart_4196994 baseEnd_4196994 := by
    simpa [prefixWord, tailWord_4196994, baseEnd_4196994] using wordTrace_append hprefix tailTrace_4196994
  have hstable : (prefixWord ++ tailWord_4196994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196994).length < 2 ^ (prefixWord ++ tailWord_4196994).sum := by decide
  have hdescent : baseEnd_4196994 < baseStart_4196994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196995 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 5]
def baseStart_4196995 : Nat := 118140960795 + 4196995 * 2 ^ 59
def prefixEnd_4196995 : Nat := 4983230072969 + 3 ^ 40 * 4196995 * 2
def baseEnd_4196995 : Nat := 2155075739516911971460877

theorem tailTrace_4196995 : CollatzResearch.WordTrace tailWord_4196995 prefixEnd_4196995 2155075739516911971460877 := by
  unfold tailWord_4196995
  simp only [CollatzResearch.WordTrace]
  refine ⟨153076983430011379524568439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102051322286674253016378959 153076983430011379524568439)
  ·
    refine ⟨229615475145017069286852659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153076983430011379524568439 229615475145017069286852659)
    ·
      refine ⟨344423212717525603930278989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229615475145017069286852659 344423212717525603930278989)
      ·
        refine ⟨129158704769072101473854621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 344423212717525603930278989 129158704769072101473854621)
        ·
          refine ⟨48434514288402038052695483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129158704769072101473854621 48434514288402038052695483)
          ·
            refine ⟨72651771432603057079043225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48434514288402038052695483 72651771432603057079043225)
            ·
              refine ⟨54488828574452292809282419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72651771432603057079043225 54488828574452292809282419)
              ·
                refine ⟨81733242861678439213923629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54488828574452292809282419 81733242861678439213923629)
                ·
                  refine ⟨30649966073129414705221361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81733242861678439213923629 30649966073129414705221361)
                  ·
                    refine ⟨22987474554847061028916021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30649966073129414705221361 22987474554847061028916021)
                    ·
                      refine ⟨2155075739516911971460877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22987474554847061028916021 2155075739516911971460877)
                      ·
                        rfl

theorem cell23_4196995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_4196995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196995 prefixEnd_4196995 := by exact prefixLift 4196995
  have htrace : WordTrace (prefixWord ++ tailWord_4196995) baseStart_4196995 baseEnd_4196995 := by
    simpa [prefixWord, tailWord_4196995, baseEnd_4196995] using wordTrace_append hprefix tailTrace_4196995
  have hstable : (prefixWord ++ tailWord_4196995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196995).length < 2 ^ (prefixWord ++ tailWord_4196995).sum := by decide
  have hdescent : baseEnd_4196995 < baseStart_4196995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197066 : List Nat := [3, 1, 2, 1, 4, 3, 1, 1, 3, 4]
def baseStart_4197066 : Nat := 118140960795 + 4197066 * 2 ^ 59
def prefixEnd_4197066 : Nat := 4983230072969 + 3 ^ 40 * 4197066 * 2
def baseEnd_4197066 : Nat := 718370732214460397891017

theorem tailTrace_4197066 : CollatzResearch.WordTrace tailWord_4197066 prefixEnd_4197066 718370732214460397891017 := by
  unfold tailWord_4197066
  simp only [CollatzResearch.WordTrace]
  refine ⟨38269893253188539662600763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102053048675169439100268701 38269893253188539662600763)
  ·
    refine ⟨57404839879782809493901145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38269893253188539662600763 57404839879782809493901145)
    ·
      refine ⟨43053629909837107120425859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57404839879782809493901145 43053629909837107120425859)
      ·
        refine ⟨64580444864755660680638789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43053629909837107120425859 64580444864755660680638789)
        ·
          refine ⟨12108833412141686377619773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64580444864755660680638789 12108833412141686377619773)
          ·
            refine ⟨4540812529553132391607415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12108833412141686377619773 4540812529553132391607415)
            ·
              refine ⟨6811218794329698587411123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4540812529553132391607415 6811218794329698587411123)
              ·
                refine ⟨10216828191494547881116685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6811218794329698587411123 10216828191494547881116685)
                ·
                  refine ⟨3831310571810455455418757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10216828191494547881116685 3831310571810455455418757)
                  ·
                    refine ⟨718370732214460397891017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3831310571810455455418757 718370732214460397891017)
                    ·
                      rfl

theorem cell23_4197066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_4197066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197066 prefixEnd_4197066 := by exact prefixLift 4197066
  have htrace : WordTrace (prefixWord ++ tailWord_4197066) baseStart_4197066 baseEnd_4197066 := by
    simpa [prefixWord, tailWord_4197066, baseEnd_4197066] using wordTrace_append hprefix tailTrace_4197066
  have hstable : (prefixWord ++ tailWord_4197066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197066).length < 2 ^ (prefixWord ++ tailWord_4197066).sum := by decide
  have hdescent : baseEnd_4197066 < baseStart_4197066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197079 : List Nat := [1, 1, 3, 2, 1, 4, 4, 1, 6]
def baseStart_4197079 : Nat := 118140960795 + 4197079 * 2 ^ 59
def prefixEnd_4197079 : Nat := 4983230072969 + 3 ^ 40 * 4197079 * 2
def baseEnd_4197079 : Nat := 239457652432432182534499

theorem tailTrace_4197079 : CollatzResearch.WordTrace tailWord_4197079 prefixEnd_4197079 239457652432432182534499 := by
  unfold tailWord_4197079
  simp only [CollatzResearch.WordTrace]
  refine ⟨153080047161707061870626291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102053364774471374580417527 153080047161707061870626291)
  ·
    refine ⟨229620070742560592805939437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153080047161707061870626291 229620070742560592805939437)
    ·
      refine ⟨86107526528460222302227289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229620070742560592805939437 86107526528460222302227289)
      ·
        refine ⟨64580644896345166726670467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86107526528460222302227289 64580644896345166726670467)
        ·
          refine ⟨96870967344517750090005701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64580644896345166726670467 96870967344517750090005701)
          ·
            refine ⟨18163306377097078141876069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96870967344517750090005701 18163306377097078141876069)
            ·
              refine ⟨3405619945705702151601763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18163306377097078141876069 3405619945705702151601763)
              ·
                refine ⟨5108429918558553227402645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3405619945705702151601763 5108429918558553227402645)
                ·
                  refine ⟨239457652432432182534499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5108429918558553227402645 239457652432432182534499)
                  ·
                    rfl

theorem cell23_4197079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 6].length) (baseStart_4197079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197079 prefixEnd_4197079 := by exact prefixLift 4197079
  have htrace : WordTrace (prefixWord ++ tailWord_4197079) baseStart_4197079 baseEnd_4197079 := by
    simpa [prefixWord, tailWord_4197079, baseEnd_4197079] using wordTrace_append hprefix tailTrace_4197079
  have hstable : (prefixWord ++ tailWord_4197079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197079).length < 2 ^ (prefixWord ++ tailWord_4197079).sum := by decide
  have hdescent : baseEnd_4197079 < baseStart_4197079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197116 : List Nat := [2, 2, 2, 1, 3, 2, 2, 2, 2, 3, 2]
def baseStart_4197116 : Nat := 118140960795 + 4197116 * 2 ^ 59
def prefixEnd_4197116 : Nat := 4983230072969 + 3 ^ 40 * 4197116 * 2
def baseEnd_4197116 : Nat := 2155137870676105998047821

theorem tailTrace_4197116 : CollatzResearch.WordTrace tailWord_4197116 prefixEnd_4197116 2155137870676105998047821 := by
  unfold tailWord_4197116
  simp only [CollatzResearch.WordTrace]
  refine ⟨76540698331286508594861601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102054264441715344793148801 76540698331286508594861601)
  ·
    refine ⟨57405523748464881446146201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76540698331286508594861601 57405523748464881446146201)
    ·
      refine ⟨43054142811348661084609651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57405523748464881446146201 43054142811348661084609651)
      ·
        refine ⟨64581214217022991626914477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43054142811348661084609651 64581214217022991626914477)
        ·
          refine ⟨24217955331383621860092929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64581214217022991626914477 24217955331383621860092929)
          ·
            refine ⟨18163466498537716395069697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24217955331383621860092929 18163466498537716395069697)
            ·
              refine ⟨13622599873903287296302273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18163466498537716395069697 13622599873903287296302273)
              ·
                refine ⟨10216949905427465472226705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13622599873903287296302273 10216949905427465472226705)
                ·
                  refine ⟨7662712429070599104170029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10216949905427465472226705 7662712429070599104170029)
                  ·
                    refine ⟨2873517160901474664063761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7662712429070599104170029 2873517160901474664063761)
                    ·
                      refine ⟨2155137870676105998047821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2873517160901474664063761 2155137870676105998047821)
                      ·
                        rfl

theorem cell23_4197116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 2, 3, 2].length) (baseStart_4197116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197116 prefixEnd_4197116 := by exact prefixLift 4197116
  have htrace : WordTrace (prefixWord ++ tailWord_4197116) baseStart_4197116 baseEnd_4197116 := by
    simpa [prefixWord, tailWord_4197116, baseEnd_4197116] using wordTrace_append hprefix tailTrace_4197116
  have hstable : (prefixWord ++ tailWord_4197116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197116).length < 2 ^ (prefixWord ++ tailWord_4197116).sum := by decide
  have hdescent : baseEnd_4197116 < baseStart_4197116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197132 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 3, 1, 5]
def baseStart_4197132 : Nat := 118140960795 + 4197132 * 2 ^ 59
def prefixEnd_4197132 : Nat := 4983230072969 + 3 ^ 40 * 4197132 * 2
def baseEnd_4197132 : Nat := 2155146086366577935447747

theorem tailTrace_4197132 : CollatzResearch.WordTrace tailWord_4197132 prefixEnd_4197132 2155146086366577935447747 := by
  unfold tailWord_4197132
  simp only [CollatzResearch.WordTrace]
  refine ⟨76540990115257525961152825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102054653487010034614870433 76540990115257525961152825)
  ·
    refine ⟨57405742586443144470864619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76540990115257525961152825 57405742586443144470864619)
    ·
      refine ⟨86108613879664716706296929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57405742586443144470864619 86108613879664716706296929)
      ·
        refine ⟨64581460409748537529722697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86108613879664716706296929 64581460409748537529722697)
        ·
          refine ⟨48436095307311403147292023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64581460409748537529722697 48436095307311403147292023)
          ·
            refine ⟨72654142960967104720938035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48436095307311403147292023 72654142960967104720938035)
            ·
              refine ⟨108981214441450657081407053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72654142960967104720938035 108981214441450657081407053)
              ·
                refine ⟨40867955415543996405527645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108981214441450657081407053 40867955415543996405527645)
                ·
                  refine ⟨15325483280828998652072867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40867955415543996405527645 15325483280828998652072867)
                  ·
                    refine ⟨22988224921243497978109301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15325483280828998652072867 22988224921243497978109301)
                    ·
                      refine ⟨2155146086366577935447747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22988224921243497978109301 2155146086366577935447747)
                      ·
                        rfl

theorem cell23_4197132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_4197132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197132 prefixEnd_4197132 := by exact prefixLift 4197132
  have htrace : WordTrace (prefixWord ++ tailWord_4197132) baseStart_4197132 baseEnd_4197132 := by
    simpa [prefixWord, tailWord_4197132, baseEnd_4197132] using wordTrace_append hprefix tailTrace_4197132
  have hstable : (prefixWord ++ tailWord_4197132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197132).length < 2 ^ (prefixWord ++ tailWord_4197132).sum := by decide
  have hdescent : baseEnd_4197132 < baseStart_4197132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197139 : List Nat := [1, 1, 1, 2, 1, 3, 3, 5, 2, 4]
def baseStart_4197139 : Nat := 118140960795 + 4197139 * 2 ^ 59
def prefixEnd_4197139 : Nat := 4983230072969 + 3 ^ 40 * 4197139 * 2
def baseEnd_4197139 : Nat := 718383226910386469353405

theorem tailTrace_4197139 : CollatzResearch.WordTrace tailWord_4197139 prefixEnd_4197139 718383226910386469353405 := by
  unfold tailWord_4197139
  simp only [CollatzResearch.WordTrace]
  refine ⟨153082235541489692117810471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102054823694326461411873647 153082235541489692117810471)
  ·
    refine ⟨229623353312234538176715707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153082235541489692117810471 229623353312234538176715707)
    ·
      refine ⟨344435029968351807265073561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229623353312234538176715707 344435029968351807265073561)
      ·
        refine ⟨258326272476263855448805171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344435029968351807265073561 258326272476263855448805171)
        ·
          refine ⟨387489408714395783173207757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258326272476263855448805171 387489408714395783173207757)
          ·
            refine ⟨145308528267898418689952909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 387489408714395783173207757 145308528267898418689952909)
            ·
              refine ⟨54490698100461907008732341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145308528267898418689952909 54490698100461907008732341)
              ·
                refine ⟨5108502946918303782068657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54490698100461907008732341 5108502946918303782068657)
                ·
                  refine ⟨3831377210188727836551493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5108502946918303782068657 3831377210188727836551493)
                  ·
                    refine ⟨718383226910386469353405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3831377210188727836551493 718383226910386469353405)
                    ·
                      rfl

theorem cell23_4197139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2, 4].length) (baseStart_4197139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197139 prefixEnd_4197139 := by exact prefixLift 4197139
  have htrace : WordTrace (prefixWord ++ tailWord_4197139) baseStart_4197139 baseEnd_4197139 := by
    simpa [prefixWord, tailWord_4197139, baseEnd_4197139] using wordTrace_append hprefix tailTrace_4197139
  have hstable : (prefixWord ++ tailWord_4197139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197139).length < 2 ^ (prefixWord ++ tailWord_4197139).sum := by decide
  have hdescent : baseEnd_4197139 < baseStart_4197139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197163 : List Nat := [1, 1, 1, 1, 2, 1, 2, 9, 1, 2, 2]
def baseStart_4197163 : Nat := 118140960795 + 4197163 * 2 ^ 59
def prefixEnd_4197163 : Nat := 4983230072969 + 3 ^ 40 * 4197163 * 2
def baseEnd_4197163 : Nat := 2155162004266867314160105

theorem tailTrace_4197163 : CollatzResearch.WordTrace tailWord_4197163 prefixEnd_4197163 2155162004266867314160105 := by
  unfold tailWord_4197163
  simp only [CollatzResearch.WordTrace]
  refine ⟨153083110893402744216684143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102055407262268496144456095 153083110893402744216684143)
  ·
    refine ⟨229624666340104116325026215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153083110893402744216684143 229624666340104116325026215)
    ·
      refine ⟨344436999510156174487539323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229624666340104116325026215 344436999510156174487539323)
      ·
        refine ⟨516655499265234261731308985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344436999510156174487539323 516655499265234261731308985)
        ·
          refine ⟨387491624448925696298481739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 516655499265234261731308985 387491624448925696298481739)
          ·
            refine ⟨581237436673388544447722609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387491624448925696298481739 581237436673388544447722609)
            ·
              refine ⟨435928077505041408335791957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 581237436673388544447722609 435928077505041408335791957)
              ·
                refine ⟨2554266079131102001967531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 435928077505041408335791957 2554266079131102001967531)
                ·
                  refine ⟨3831399118696653002951297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2554266079131102001967531 3831399118696653002951297)
                  ·
                    refine ⟨2873549339022489752213473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3831399118696653002951297 2873549339022489752213473)
                    ·
                      refine ⟨2155162004266867314160105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2873549339022489752213473 2155162004266867314160105)
                      ·
                        rfl

theorem cell23_4197163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9, 1, 2, 2].length) (baseStart_4197163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197163 prefixEnd_4197163 := by exact prefixLift 4197163
  have htrace : WordTrace (prefixWord ++ tailWord_4197163) baseStart_4197163 baseEnd_4197163 := by
    simpa [prefixWord, tailWord_4197163, baseEnd_4197163] using wordTrace_append hprefix tailTrace_4197163
  have hstable : (prefixWord ++ tailWord_4197163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197163).length < 2 ^ (prefixWord ++ tailWord_4197163).sum := by decide
  have hdescent : baseEnd_4197163 < baseStart_4197163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197173 : List Nat := [1, 3, 3, 1, 3, 3, 1, 2, 2, 4]
def baseStart_4197173 : Nat := 118140960795 + 4197173 * 2 ^ 59
def prefixEnd_4197173 : Nat := 4983230072969 + 3 ^ 40 * 4197173 * 2
def baseEnd_4197173 : Nat := 718389046357804091678353

theorem tailTrace_4197173 : CollatzResearch.WordTrace tailWord_4197173 prefixEnd_4197173 718389046357804091678353 := by
  unfold tailWord_4197173
  simp only [CollatzResearch.WordTrace]
  refine ⟨153083475623366515924548173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102055650415577677283032115 153083475623366515924548173)
  ·
    refine ⟨57406303358762443471705565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153083475623366515924548173 57406303358762443471705565)
    ·
      refine ⟨21527363759535916301889587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57406303358762443471705565 21527363759535916301889587)
      ·
        refine ⟨32291045639303874452834381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21527363759535916301889587 32291045639303874452834381)
        ·
          refine ⟨12109142114738952919812893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32291045639303874452834381 12109142114738952919812893)
          ·
            refine ⟨4540928293027107344929835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12109142114738952919812893 4540928293027107344929835)
            ·
              refine ⟨6811392439540661017394753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4540928293027107344929835 6811392439540661017394753)
              ·
                refine ⟨5108544329655495763046065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6811392439540661017394753 5108544329655495763046065)
                ·
                  refine ⟨3831408247241621822284549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5108544329655495763046065 3831408247241621822284549)
                  ·
                    refine ⟨718389046357804091678353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3831408247241621822284549 718389046357804091678353)
                    ·
                      rfl

theorem cell23_4197173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_4197173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197173 prefixEnd_4197173 := by exact prefixLift 4197173
  have htrace : WordTrace (prefixWord ++ tailWord_4197173) baseStart_4197173 baseEnd_4197173 := by
    simpa [prefixWord, tailWord_4197173, baseEnd_4197173] using wordTrace_append hprefix tailTrace_4197173
  have hstable : (prefixWord ++ tailWord_4197173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197173).length < 2 ^ (prefixWord ++ tailWord_4197173).sum := by decide
  have hdescent : baseEnd_4197173 < baseStart_4197173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197189 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 2, 7, 2]
def baseStart_4197189 : Nat := 118140960795 + 4197189 * 2 ^ 59
def prefixEnd_4197189 : Nat := 4983230072969 + 3 ^ 40 * 4197189 * 2
def baseEnd_4197189 : Nat := 2155175354763884212434985

theorem tailTrace_4197189 : CollatzResearch.WordTrace tailWord_4197189 prefixEnd_4197189 2155175354763884212434985 := by
  unfold tailWord_4197189
  simp only [CollatzResearch.WordTrace]
  refine ⟨153084059191308550657130621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102056039460872367104753747 153084059191308550657130621)
  ·
    refine ⟨57406522196740706496423983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153084059191308550657130621 57406522196740706496423983)
    ·
      refine ⟨86109783295111059744635975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57406522196740706496423983 86109783295111059744635975)
      ·
        refine ⟨129164674942666589616953963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86109783295111059744635975 129164674942666589616953963)
        ·
          refine ⟨193747012413999884425430945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129164674942666589616953963 193747012413999884425430945)
          ·
            refine ⟨145310259310499913319073209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193747012413999884425430945 145310259310499913319073209)
            ·
              refine ⟨108982694482874934989304907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145310259310499913319073209 108982694482874934989304907)
              ·
                refine ⟨163474041724312402483957361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108982694482874934989304907 163474041724312402483957361)
                ·
                  refine ⟨122605531293234301862968021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163474041724312402483957361 122605531293234301862968021)
                  ·
                    refine ⟨2873567139685178949913313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 122605531293234301862968021 2873567139685178949913313)
                    ·
                      refine ⟨2155175354763884212434985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2873567139685178949913313 2155175354763884212434985)
                      ·
                        rfl

theorem cell23_4197189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 7, 2].length) (baseStart_4197189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197189 prefixEnd_4197189 := by exact prefixLift 4197189
  have htrace : WordTrace (prefixWord ++ tailWord_4197189) baseStart_4197189 baseEnd_4197189 := by
    simpa [prefixWord, tailWord_4197189, baseEnd_4197189] using wordTrace_append hprefix tailTrace_4197189
  have hstable : (prefixWord ++ tailWord_4197189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197189).length < 2 ^ (prefixWord ++ tailWord_4197189).sum := by decide
  have hdescent : baseEnd_4197189 < baseStart_4197189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197190 : List Nat := [6, 1, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_4197190 : Nat := 118140960795 + 4197190 * 2 ^ 59
def prefixEnd_4197190 : Nat := 4983230072969 + 3 ^ 40 * 4197190 * 2
def baseEnd_4197190 : Nat := 718391956081512902840827

theorem tailTrace_4197190 : CollatzResearch.WordTrace tailWord_4197190 prefixEnd_4197190 718391956081512902840827 := by
  unfold tailWord_4197190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4783877989509528994622407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 102056063776203285218611349 4783877989509528994622407)
  ·
    refine ⟨7175816984264293491933611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4783877989509528994622407 7175816984264293491933611)
    ·
      refine ⟨10763725476396440237900417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7175816984264293491933611 10763725476396440237900417)
      ·
        refine ⟨8072794107297330178425313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10763725476396440237900417 8072794107297330178425313)
        ·
          refine ⟨6054595580472997633818985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8072794107297330178425313 6054595580472997633818985)
          ·
            refine ⟨4540946685354748225364239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6054595580472997633818985 4540946685354748225364239)
            ·
              refine ⟨6811420028032122338046359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4540946685354748225364239 6811420028032122338046359)
              ·
                refine ⟨10217130042048183507069539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6811420028032122338046359 10217130042048183507069539)
                ·
                  refine ⟨15325695063072275260604309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10217130042048183507069539 15325695063072275260604309)
                  ·
                    refine ⟨718391956081512902840827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15325695063072275260604309 718391956081512902840827)
                    ·
                      rfl

theorem cell23_4197190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_4197190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197190 prefixEnd_4197190 := by exact prefixLift 4197190
  have htrace : WordTrace (prefixWord ++ tailWord_4197190) baseStart_4197190 baseEnd_4197190 := by
    simpa [prefixWord, tailWord_4197190, baseEnd_4197190] using wordTrace_append hprefix tailTrace_4197190
  have hstable : (prefixWord ++ tailWord_4197190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197190).length < 2 ^ (prefixWord ++ tailWord_4197190).sum := by decide
  have hdescent : baseEnd_4197190 < baseStart_4197190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197196 : List Nat := [2, 2, 1, 3, 3, 1, 3, 1, 1, 3, 3]
def baseStart_4197196 : Nat := 118140960795 + 4197196 * 2 ^ 59
def prefixEnd_4197196 : Nat := 4983230072969 + 3 ^ 40 * 4197196 * 2
def baseEnd_4197196 : Nat := 2155178949128465685047453

theorem tailTrace_4197196 : CollatzResearch.WordTrace tailWord_4197196 prefixEnd_4197196 2155178949128465685047453 := by
  unfold tailWord_4197196
  simp only [CollatzResearch.WordTrace]
  refine ⟨76542157251141595426317721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102056209668188793901756961 76542157251141595426317721)
  ·
    refine ⟨57406617938356196569738291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76542157251141595426317721 57406617938356196569738291)
    ·
      refine ⟨86109926907534294854607437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57406617938356196569738291 86109926907534294854607437)
      ·
        refine ⟨32291222590325360570477789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86109926907534294854607437 32291222590325360570477789)
        ·
          refine ⟨12109208471372010213929171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32291222590325360570477789 12109208471372010213929171)
          ·
            refine ⟨18163812707058015320893757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12109208471372010213929171 18163812707058015320893757)
            ·
              refine ⟨6811429765146755745335159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18163812707058015320893757 6811429765146755745335159)
              ·
                refine ⟨10217144647720133618002739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6811429765146755745335159 10217144647720133618002739)
                ·
                  refine ⟨15325716971580200427004109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10217144647720133618002739 15325716971580200427004109)
                  ·
                    refine ⟨5747143864342575160126541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15325716971580200427004109 5747143864342575160126541)
                    ·
                      refine ⟨2155178949128465685047453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5747143864342575160126541 2155178949128465685047453)
                      ·
                        rfl

theorem cell23_4197196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_4197196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197196 prefixEnd_4197196 := by exact prefixLift 4197196
  have htrace : WordTrace (prefixWord ++ tailWord_4197196) baseStart_4197196 baseEnd_4197196 := by
    simpa [prefixWord, tailWord_4197196, baseEnd_4197196] using wordTrace_append hprefix tailTrace_4197196
  have hstable : (prefixWord ++ tailWord_4197196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197196).length < 2 ^ (prefixWord ++ tailWord_4197196).sum := by decide
  have hdescent : baseEnd_4197196 < baseStart_4197196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197223 : List Nat := [1, 1, 5, 1, 2, 2, 2, 3, 1, 3, 2]
def baseStart_4197223 : Nat := 118140960795 + 4197223 * 2 ^ 59
def prefixEnd_4197223 : Nat := 4983230072969 + 3 ^ 40 * 4197223 * 2
def baseEnd_4197223 : Nat := 2155192813106137079409829

theorem tailTrace_4197223 : CollatzResearch.WordTrace tailWord_4197223 prefixEnd_4197223 2155192813106137079409829 := by
  unfold tailWord_4197223
  simp only [CollatzResearch.WordTrace]
  refine ⟨153085299273185374463868323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102056866182123582975912215 153085299273185374463868323)
  ·
    refine ⟨229627948909778061695802485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153085299273185374463868323 229627948909778061695802485)
    ·
      refine ⟨21527620210291693283981483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 229627948909778061695802485 21527620210291693283981483)
      ·
        refine ⟨32291430315437539925972225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21527620210291693283981483 32291430315437539925972225)
        ·
          refine ⟨24218572736578154944479169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32291430315437539925972225 24218572736578154944479169)
          ·
            refine ⟨18163929552433616208359377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24218572736578154944479169 18163929552433616208359377)
            ·
              refine ⟨13622947164325212156269533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18163929552433616208359377 13622947164325212156269533)
              ·
                refine ⟨5108605186621954558601075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13622947164325212156269533 5108605186621954558601075)
                ·
                  refine ⟨7662907779932931837901613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5108605186621954558601075 7662907779932931837901613)
                  ·
                    refine ⟨2873590417474849439213105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7662907779932931837901613 2873590417474849439213105)
                    ·
                      refine ⟨2155192813106137079409829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2873590417474849439213105 2155192813106137079409829)
                      ·
                        rfl

theorem cell23_4197223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_4197223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197223 prefixEnd_4197223 := by exact prefixLift 4197223
  have htrace : WordTrace (prefixWord ++ tailWord_4197223) baseStart_4197223 baseEnd_4197223 := by
    simpa [prefixWord, tailWord_4197223, baseEnd_4197223] using wordTrace_append hprefix tailTrace_4197223
  have hstable : (prefixWord ++ tailWord_4197223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197223).length < 2 ^ (prefixWord ++ tailWord_4197223).sum := by decide
  have hdescent : baseEnd_4197223 < baseStart_4197223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197287 : List Nat := [1, 1, 6, 1, 3, 1, 2, 2, 2, 2, 2]
def baseStart_4197287 : Nat := 118140960795 + 4197287 * 2 ^ 59
def prefixEnd_4197287 : Nat := 4983230072969 + 3 ^ 40 * 4197287 * 2
def baseEnd_4197287 : Nat := 2155225675868024829009535

theorem tailTrace_4197287 : CollatzResearch.WordTrace tailWord_4197287 prefixEnd_4197287 2155225675868024829009535 := by
  unfold tailWord_4197287
  simp only [CollatzResearch.WordTrace]
  refine ⟨153087633544953513394198115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102058422363302342262798743 153087633544953513394198115)
  ·
    refine ⟨229631450317430270091297173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153087633544953513394198115 229631450317430270091297173)
    ·
      refine ⟨10763974233629543910529555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 229631450317430270091297173 10763974233629543910529555)
      ·
        refine ⟨16145961350444315865794333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10763974233629543910529555 16145961350444315865794333)
        ·
          refine ⟨6054735506416618449672875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16145961350444315865794333 6054735506416618449672875)
          ·
            refine ⟨9082103259624927674509313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6054735506416618449672875 9082103259624927674509313)
            ·
              refine ⟨6811577444718695755881985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9082103259624927674509313 6811577444718695755881985)
              ·
                refine ⟨5108683083539021816911489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6811577444718695755881985 5108683083539021816911489)
                ·
                  refine ⟨3831512312654266362683617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5108683083539021816911489 3831512312654266362683617)
                  ·
                    refine ⟨2873634234490699772012713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3831512312654266362683617 2873634234490699772012713)
                    ·
                      refine ⟨2155225675868024829009535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2873634234490699772012713 2155225675868024829009535)
                      ·
                        rfl

theorem cell23_4197287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_4197287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197287 prefixEnd_4197287 := by exact prefixLift 4197287
  have htrace : WordTrace (prefixWord ++ tailWord_4197287) baseStart_4197287 baseEnd_4197287 := by
    simpa [prefixWord, tailWord_4197287, baseEnd_4197287] using wordTrace_append hprefix tailTrace_4197287
  have hstable : (prefixWord ++ tailWord_4197287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197287).length < 2 ^ (prefixWord ++ tailWord_4197287).sum := by decide
  have hdescent : baseEnd_4197287 < baseStart_4197287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197289 : List Nat := [1, 2, 1, 1, 1, 1, 5, 4, 2, 5]
def baseStart_4197289 : Nat := 118140960795 + 4197289 * 2 ^ 59
def prefixEnd_4197289 : Nat := 4983230072969 + 3 ^ 40 * 4197289 * 2
def baseEnd_4197289 : Nat := 718408900943111273728175

theorem tailTrace_4197289 : CollatzResearch.WordTrace tailWord_4197289 prefixEnd_4197289 718408900943111273728175 := by
  unfold tailWord_4197289
  simp only [CollatzResearch.WordTrace]
  refine ⟨153087706490946267735770921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102058470993964178490513947 153087706490946267735770921)
  ·
    refine ⟨114815779868209700801828191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153087706490946267735770921 114815779868209700801828191)
    ·
      refine ⟨172223669802314551202742287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114815779868209700801828191 172223669802314551202742287)
      ·
        refine ⟨258335504703471826804113431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172223669802314551202742287 258335504703471826804113431)
        ·
          refine ⟨387503257055207740206170147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258335504703471826804113431 387503257055207740206170147)
          ·
            refine ⟨581254885582811610309255221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387503257055207740206170147 581254885582811610309255221)
            ·
              refine ⟨54492645523388588466492677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 581254885582811610309255221 54492645523388588466492677)
              ·
                refine ⟨10217371035635360337467377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54492645523388588466492677 10217371035635360337467377)
                ·
                  refine ⟨7663028276726520253100533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10217371035635360337467377 7663028276726520253100533)
                  ·
                    refine ⟨718408900943111273728175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7663028276726520253100533 718408900943111273728175)
                    ·
                      rfl

theorem cell23_4197289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 5].length) (baseStart_4197289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197289 prefixEnd_4197289 := by exact prefixLift 4197289
  have htrace : WordTrace (prefixWord ++ tailWord_4197289) baseStart_4197289 baseEnd_4197289 := by
    simpa [prefixWord, tailWord_4197289, baseEnd_4197289] using wordTrace_append hprefix tailTrace_4197289
  have hstable : (prefixWord ++ tailWord_4197289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197289).length < 2 ^ (prefixWord ++ tailWord_4197289).sum := by decide
  have hdescent : baseEnd_4197289 < baseStart_4197289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197326 : List Nat := [4, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4]
def baseStart_4197326 : Nat := 118140960795 + 4197326 * 2 ^ 59
def prefixEnd_4197326 : Nat := 4983230072969 + 3 ^ 40 * 4197326 * 2
def baseEnd_4197326 : Nat := 2155245701613550176421855

theorem tailTrace_4197326 : CollatzResearch.WordTrace tailWord_4197326 prefixEnd_4197326 2155245701613550176421855 := by
  unfold tailWord_4197326
  simp only [CollatzResearch.WordTrace]
  refine ⟨19136131998976527881858479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102059370661208148703245221 19136131998976527881858479)
  ·
    refine ⟨28704197998464791822787719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19136131998976527881858479 28704197998464791822787719)
    ·
      refine ⟨43056296997697187734181579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28704197998464791822787719 43056296997697187734181579)
      ·
        refine ⟨64584445496545781601272369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43056296997697187734181579 64584445496545781601272369)
        ·
          refine ⟨48438334122409336200954277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64584445496545781601272369 48438334122409336200954277)
          ·
            refine ⟨9082187647951750537678927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48438334122409336200954277 9082187647951750537678927)
            ·
              refine ⟨13623281471927625806518391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9082187647951750537678927 13623281471927625806518391)
              ·
                refine ⟨20434922207891438709777587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13623281471927625806518391 20434922207891438709777587)
                ·
                  refine ⟨30652383311837158064666381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20434922207891438709777587 30652383311837158064666381)
                  ·
                    refine ⟨11494643741938934274249893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30652383311837158064666381 11494643741938934274249893)
                    ·
                      refine ⟨2155245701613550176421855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11494643741938934274249893 2155245701613550176421855)
                      ·
                        rfl

theorem cell23_4197326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_4197326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197326 prefixEnd_4197326 := by exact prefixLift 4197326
  have htrace : WordTrace (prefixWord ++ tailWord_4197326) baseStart_4197326 baseEnd_4197326 := by
    simpa [prefixWord, tailWord_4197326, baseEnd_4197326] using wordTrace_append hprefix tailTrace_4197326
  have hstable : (prefixWord ++ tailWord_4197326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197326).length < 2 ^ (prefixWord ++ tailWord_4197326).sum := by decide
  have hdescent : baseEnd_4197326 < baseStart_4197326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197369 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 1, 2, 6]
def baseStart_4197369 : Nat := 118140960795 + 4197369 * 2 ^ 59
def prefixEnd_4197369 : Nat := 4983230072969 + 3 ^ 40 * 4197369 * 2
def baseEnd_4197369 : Nat := 2155267781281693508184157

theorem tailTrace_4197369 : CollatzResearch.WordTrace tailWord_4197369 prefixEnd_4197369 2155267781281693508184157 := by
  unfold tailWord_4197369
  simp only [CollatzResearch.WordTrace]
  refine ⟨153090624330656441398683161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102060416220437627599122107 153090624330656441398683161)
  ·
    refine ⟨114817968247992331049012371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153090624330656441398683161 114817968247992331049012371)
    ·
      refine ⟨172226952371988496573518557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114817968247992331049012371 172226952371988496573518557)
      ·
        refine ⟨64585107139495686215069459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172226952371988496573518557 64585107139495686215069459)
        ·
          refine ⟨96877660709243529322604189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64585107139495686215069459 96877660709243529322604189)
          ·
            refine ⟨36329122765966323495976571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96877660709243529322604189 36329122765966323495976571)
            ·
              refine ⟨54493684148949485243964857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36329122765966323495976571 54493684148949485243964857)
              ·
                refine ⟨40870263111712113932973643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54493684148949485243964857 40870263111712113932973643)
                ·
                  refine ⟨61305394667568170899460465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40870263111712113932973643 61305394667568170899460465)
                  ·
                    refine ⟨45979046000676128174595349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61305394667568170899460465 45979046000676128174595349)
                    ·
                      refine ⟨2155267781281693508184157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45979046000676128174595349 2155267781281693508184157)
                      ·
                        rfl

theorem cell23_4197369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_4197369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197369 prefixEnd_4197369 := by exact prefixLift 4197369
  have htrace : WordTrace (prefixWord ++ tailWord_4197369) baseStart_4197369 baseEnd_4197369 := by
    simpa [prefixWord, tailWord_4197369, baseEnd_4197369] using wordTrace_append hprefix tailTrace_4197369
  have hstable : (prefixWord ++ tailWord_4197369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197369).length < 2 ^ (prefixWord ++ tailWord_4197369).sum := by decide
  have hdescent : baseEnd_4197369 < baseStart_4197369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197410 : List Nat := [3, 3, 1, 1, 1, 3, 3, 1, 3, 1, 3]
def baseStart_4197410 : Nat := 118140960795 + 4197410 * 2 ^ 59
def prefixEnd_4197410 : Nat := 4983230072969 + 3 ^ 40 * 4197410 * 2
def baseEnd_4197410 : Nat := 2155288833988527847771469

theorem tailTrace_4197410 : CollatzResearch.WordTrace tailWord_4197410 prefixEnd_4197410 2155288833988527847771469 := by
  unfold tailWord_4197410
  simp only [CollatzResearch.WordTrace]
  refine ⟨38273029930876976350231421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102061413149005270267283789 38273029930876976350231421)
  ·
    refine ⟨14352386224078866131336783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38273029930876976350231421 14352386224078866131336783)
    ·
      refine ⟨21528579336118299197005175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14352386224078866131336783 21528579336118299197005175)
      ·
        refine ⟨32292869004177448795507763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21528579336118299197005175 32292869004177448795507763)
        ·
          refine ⟨48439303506266173193261645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32292869004177448795507763 48439303506266173193261645)
          ·
            refine ⟨18164738814849814947473117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48439303506266173193261645 18164738814849814947473117)
            ·
              refine ⟨6811777055568680605302419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18164738814849814947473117 6811777055568680605302419)
              ·
                refine ⟨10217665583353020907953629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6811777055568680605302419 10217665583353020907953629)
                ·
                  refine ⟨3831624593757382840482611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10217665583353020907953629 3831624593757382840482611)
                  ·
                    refine ⟨5747436890636074260723917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3831624593757382840482611 5747436890636074260723917)
                    ·
                      refine ⟨2155288833988527847771469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5747436890636074260723917 2155288833988527847771469)
                      ·
                        rfl

theorem cell23_4197410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_4197410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197410 prefixEnd_4197410 := by exact prefixLift 4197410
  have htrace : WordTrace (prefixWord ++ tailWord_4197410) baseStart_4197410 baseEnd_4197410 := by
    simpa [prefixWord, tailWord_4197410, baseEnd_4197410] using wordTrace_append hprefix tailTrace_4197410
  have hstable : (prefixWord ++ tailWord_4197410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197410).length < 2 ^ (prefixWord ++ tailWord_4197410).sum := by decide
  have hdescent : baseEnd_4197410 < baseStart_4197410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197426 : List Nat := [3, 2, 1, 1, 2, 2, 2, 3, 1, 6]
def baseStart_4197426 : Nat := 118140960795 + 4197426 * 2 ^ 59
def prefixEnd_4197426 : Nat := 4983230072969 + 3 ^ 40 * 4197426 * 2
def baseEnd_4197426 : Nat := 718432349892999928390465

theorem tailTrace_4197426 : CollatzResearch.WordTrace tailWord_4197426 prefixEnd_4197426 718432349892999928390465 := by
  unfold tailWord_4197426
  simp only [CollatzResearch.WordTrace]
  refine ⟨38273175822862485033377033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102061802194299960089005421 38273175822862485033377033)
  ·
    refine ⟨28704881867146863775032775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38273175822862485033377033 28704881867146863775032775)
    ·
      refine ⟨43057322800720295662549163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28704881867146863775032775 43057322800720295662549163)
      ·
        refine ⟨64585984201080443493823745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43057322800720295662549163 64585984201080443493823745)
        ·
          refine ⟨48439488150810332620367809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64585984201080443493823745 48439488150810332620367809)
          ·
            refine ⟨36329616113107749465275857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48439488150810332620367809 36329616113107749465275857)
            ·
              refine ⟨27247212084830812098956893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36329616113107749465275857 27247212084830812098956893)
              ·
                refine ⟨10217704531811554537108835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27247212084830812098956893 10217704531811554537108835)
                ·
                  refine ⟨15326556797717331805663253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10217704531811554537108835 15326556797717331805663253)
                  ·
                    refine ⟨718432349892999928390465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15326556797717331805663253 718432349892999928390465)
                    ·
                      rfl

theorem cell23_4197426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_4197426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197426 prefixEnd_4197426 := by exact prefixLift 4197426
  have htrace : WordTrace (prefixWord ++ tailWord_4197426) baseStart_4197426 baseEnd_4197426 := by
    simpa [prefixWord, tailWord_4197426, baseEnd_4197426] using wordTrace_append hprefix tailTrace_4197426
  have hstable : (prefixWord ++ tailWord_4197426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197426).length < 2 ^ (prefixWord ++ tailWord_4197426).sum := by decide
  have hdescent : baseEnd_4197426 < baseStart_4197426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197430 : List Nat := [5, 1, 2, 1, 1, 2, 3, 2, 1, 5]
def baseStart_4197430 : Nat := 118140960795 + 4197430 * 2 ^ 59
def prefixEnd_4197430 : Nat := 4983230072969 + 3 ^ 40 * 4197430 * 2
def baseEnd_4197430 : Nat := 718433034533872589840459

theorem tailTrace_4197430 : CollatzResearch.WordTrace tailWord_4197430 prefixEnd_4197430 718433034533872589840459 := by
  unfold tailWord_4197430
  simp only [CollatzResearch.WordTrace]
  refine ⟨9568303073964715551040859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102061899455623632544435829 9568303073964715551040859)
  ·
    refine ⟨14352454610947073326561289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9568303073964715551040859 14352454610947073326561289)
    ·
      refine ⟨10764340958210304994920967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14352454610947073326561289 10764340958210304994920967)
      ·
        refine ⟨16146511437315457492381451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10764340958210304994920967 16146511437315457492381451)
        ·
          refine ⟨24219767155973186238572177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16146511437315457492381451 24219767155973186238572177)
          ·
            refine ⟨18164825366979889678929133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24219767155973186238572177 18164825366979889678929133)
            ·
              refine ⟨6811809512617458629598425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18164825366979889678929133 6811809512617458629598425)
              ·
                refine ⟨5108857134463093972198819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6811809512617458629598425 5108857134463093972198819)
                ·
                  refine ⟨7663285701694640958298229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5108857134463093972198819 7663285701694640958298229)
                  ·
                    refine ⟨718433034533872589840459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7663285701694640958298229 718433034533872589840459)
                    ·
                      rfl

theorem cell23_4197430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_4197430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197430 prefixEnd_4197430 := by exact prefixLift 4197430
  have htrace : WordTrace (prefixWord ++ tailWord_4197430) baseStart_4197430 baseEnd_4197430 := by
    simpa [prefixWord, tailWord_4197430, baseEnd_4197430] using wordTrace_append hprefix tailTrace_4197430
  have hstable : (prefixWord ++ tailWord_4197430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197430).length < 2 ^ (prefixWord ++ tailWord_4197430).sum := by decide
  have hdescent : baseEnd_4197430 < baseStart_4197430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197433 : List Nat := [1, 2, 1, 5, 2, 2, 1, 1, 3, 1, 4]
def baseStart_4197433 : Nat := 118140960795 + 4197433 * 2 ^ 59
def prefixEnd_4197433 : Nat := 4983230072969 + 3 ^ 40 * 4197433 * 2
def baseEnd_4197433 : Nat := 2155300644043581257783863

theorem tailTrace_4197433 : CollatzResearch.WordTrace tailWord_4197433 prefixEnd_4197433 2155300644043581257783863 := by
  unfold tailWord_4197433
  simp only [CollatzResearch.WordTrace]
  refine ⟨153092958602424580329012953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102061972401616386886008635 153092958602424580329012953)
  ·
    refine ⟨114819718951818435246759715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153092958602424580329012953 114819718951818435246759715)
    ·
      refine ⟨172229578427727652870139573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114819718951818435246759715 172229578427727652870139573)
      ·
        refine ⟨16146522977599467456575585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 172229578427727652870139573 16146522977599467456575585)
        ·
          refine ⟨12109892233199600592431689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16146522977599467456575585 12109892233199600592431689)
          ·
            refine ⟨9082419174899700444323767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12109892233199600592431689 9082419174899700444323767)
            ·
              refine ⟨13623628762349550666485651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9082419174899700444323767 13623628762349550666485651)
              ·
                refine ⟨20435443143524325999728477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13623628762349550666485651 20435443143524325999728477)
                ·
                  refine ⟨7663291178821622249898179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20435443143524325999728477 7663291178821622249898179)
                  ·
                    refine ⟨11494936768232433374847269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7663291178821622249898179 11494936768232433374847269)
                    ·
                      refine ⟨2155300644043581257783863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11494936768232433374847269 2155300644043581257783863)
                      ·
                        rfl

theorem cell23_4197433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_4197433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197433 prefixEnd_4197433 := by exact prefixLift 4197433
  have htrace : WordTrace (prefixWord ++ tailWord_4197433) baseStart_4197433 baseEnd_4197433 := by
    simpa [prefixWord, tailWord_4197433, baseEnd_4197433] using wordTrace_append hprefix tailTrace_4197433
  have hstable : (prefixWord ++ tailWord_4197433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197433).length < 2 ^ (prefixWord ++ tailWord_4197433).sum := by decide
  have hdescent : baseEnd_4197433 < baseStart_4197433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197523 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 3, 4, 2]
def baseStart_4197523 : Nat := 118140960795 + 4197523 * 2 ^ 59
def prefixEnd_4197523 : Nat := 4983230072969 + 3 ^ 40 * 4197523 * 2
def baseEnd_4197523 : Nat := 2155346857302485905658449

theorem tailTrace_4197523 : CollatzResearch.WordTrace tailWord_4197523 prefixEnd_4197523 2155346857302485905658449 := by
  unfold tailWord_4197523
  simp only [CollatzResearch.WordTrace]
  refine ⟨153096241172098525699789223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102064160781399017133192815 153096241172098525699789223)
  ·
    refine ⟨229644361758147788549683835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153096241172098525699789223 229644361758147788549683835)
    ·
      refine ⟨344466542637221682824525753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229644361758147788549683835 344466542637221682824525753)
      ·
        refine ⟨258349906977916262118394315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344466542637221682824525753 258349906977916262118394315)
        ·
          refine ⟨387524860466874393177591473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258349906977916262118394315 387524860466874393177591473)
          ·
            refine ⟨290643645350155794883193605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387524860466874393177591473 290643645350155794883193605)
            ·
              refine ⟨54495683503154211540598801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 290643645350155794883193605 54495683503154211540598801)
              ·
                refine ⟨40871762627365658655449101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54495683503154211540598801 40871762627365658655449101)
                ·
                  refine ⟨15326910985262121995793413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40871762627365658655449101 15326910985262121995793413)
                  ·
                    refine ⟨2873795809736647874211265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15326910985262121995793413 2873795809736647874211265)
                    ·
                      refine ⟨2155346857302485905658449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2873795809736647874211265 2155346857302485905658449)
                      ·
                        rfl

theorem cell23_4197523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 4, 2].length) (baseStart_4197523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197523 prefixEnd_4197523 := by exact prefixLift 4197523
  have htrace : WordTrace (prefixWord ++ tailWord_4197523) baseStart_4197523 baseEnd_4197523 := by
    simpa [prefixWord, tailWord_4197523, baseEnd_4197523] using wordTrace_append hprefix tailTrace_4197523
  have hstable : (prefixWord ++ tailWord_4197523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197523).length < 2 ^ (prefixWord ++ tailWord_4197523).sum := by decide
  have hdescent : baseEnd_4197523 < baseStart_4197523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197563 : List Nat := [1, 1, 1, 1, 1, 2, 4, 7, 5]
def baseStart_4197563 : Nat := 118140960795 + 4197563 * 2 ^ 59
def prefixEnd_4197563 : Nat := 4983230072969 + 3 ^ 40 * 4197563 * 2
def baseEnd_4197563 : Nat := 239485266280962861017585

theorem tailTrace_4197563 : CollatzResearch.WordTrace tailWord_4197563 prefixEnd_4197563 239485266280962861017585 := by
  unfold tailWord_4197563
  simp only [CollatzResearch.WordTrace]
  refine ⟨153097700091953612531245343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102065133394635741687496895 153097700091953612531245343)
  ·
    refine ⟨229646550137930418796868015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153097700091953612531245343 229646550137930418796868015)
    ·
      refine ⟨344469825206895628195302023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229646550137930418796868015 344469825206895628195302023)
      ·
        refine ⟨516704737810343442292953035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344469825206895628195302023 516704737810343442292953035)
        ·
          refine ⟨775057106715515163439429553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516704737810343442292953035 775057106715515163439429553)
          ·
            refine ⟨581292830036636372579572165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 775057106715515163439429553 581292830036636372579572165)
            ·
              refine ⟨108992405631869319858669781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 581292830036636372579572165 108992405631869319858669781)
              ·
                refine ⟨2554509506996937184187573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 108992405631869319858669781 2554509506996937184187573)
                ·
                  refine ⟨239485266280962861017585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2554509506996937184187573 239485266280962861017585)
                  ·
                    rfl

theorem cell23_4197563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7, 5].length) (baseStart_4197563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197563 prefixEnd_4197563 := by exact prefixLift 4197563
  have htrace : WordTrace (prefixWord ++ tailWord_4197563) baseStart_4197563 baseEnd_4197563 := by
    simpa [prefixWord, tailWord_4197563, baseEnd_4197563] using wordTrace_append hprefix tailTrace_4197563
  have hstable : (prefixWord ++ tailWord_4197563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197563).length < 2 ^ (prefixWord ++ tailWord_4197563).sum := by decide
  have hdescent : baseEnd_4197563 < baseStart_4197563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197610 : List Nat := [3, 1, 3, 1, 1, 4, 2, 1, 2, 5]
def baseStart_4197610 : Nat := 118140960795 + 4197610 * 2 ^ 59
def prefixEnd_4197610 : Nat := 4983230072969 + 3 ^ 40 * 4197610 * 2
def baseEnd_4197610 : Nat := 718463843373142355090183

theorem tailTrace_4197610 : CollatzResearch.WordTrace tailWord_4197610 prefixEnd_4197610 718463843373142355090183 := by
  unfold tailWord_4197610
  simp only [CollatzResearch.WordTrace]
  refine ⟨38274853580695834889551571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102066276215188893038804189 38274853580695834889551571)
  ·
    refine ⟨57412280371043752334327357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38274853580695834889551571 57412280371043752334327357)
    ·
      refine ⟨21529605139141407125372759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57412280371043752334327357 21529605139141407125372759)
      ·
        refine ⟨32294407708712110688059139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21529605139141407125372759 32294407708712110688059139)
        ·
          refine ⟨48441611563068166032088709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32294407708712110688059139 48441611563068166032088709)
          ·
            refine ⟨9082802168075281131016633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48441611563068166032088709 9082802168075281131016633)
            ·
              refine ⟨6812101626056460848262475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9082802168075281131016633 6812101626056460848262475)
              ·
                refine ⟨10218152439084691272393713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6812101626056460848262475 10218152439084691272393713)
                ·
                  refine ⟨7663614329313518454295285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10218152439084691272393713 7663614329313518454295285)
                  ·
                    refine ⟨718463843373142355090183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7663614329313518454295285 718463843373142355090183)
                    ·
                      rfl

theorem cell23_4197610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_4197610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197610 prefixEnd_4197610 := by exact prefixLift 4197610
  have htrace : WordTrace (prefixWord ++ tailWord_4197610) baseStart_4197610 baseEnd_4197610 := by
    simpa [prefixWord, tailWord_4197610, baseEnd_4197610] using wordTrace_append hprefix tailTrace_4197610
  have hstable : (prefixWord ++ tailWord_4197610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197610).length < 2 ^ (prefixWord ++ tailWord_4197610).sum := by decide
  have hdescent : baseEnd_4197610 < baseStart_4197610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197616 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 9]
def baseStart_4197616 : Nat := 118140960795 + 4197616 * 2 ^ 59
def prefixEnd_4197616 : Nat := 4983230072969 + 3 ^ 40 * 4197616 * 2
def baseEnd_4197616 : Nat := 2155394611003354041795521

theorem tailTrace_4197616 : CollatzResearch.WordTrace tailWord_4197616 prefixEnd_4197616 2155394611003354041795521 := by
  unfold tailWord_4197616
  simp only [CollatzResearch.WordTrace]
  refine ⟨76549816580380801291462351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102066422107174401721949801 76549816580380801291462351)
  ·
    refine ⟨114824724870571201937193527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76549816580380801291462351 114824724870571201937193527)
    ·
      refine ⟨172237087305856802905790291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114824724870571201937193527 172237087305856802905790291)
      ·
        refine ⟨258355630958785204358685437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172237087305856802905790291 258355630958785204358685437)
        ·
          refine ⟨96883361609544451634507039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 258355630958785204358685437 96883361609544451634507039)
          ·
            refine ⟨145325042414316677451760559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96883361609544451634507039 145325042414316677451760559)
            ·
              refine ⟨217987563621475016177640839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145325042414316677451760559 217987563621475016177640839)
              ·
                refine ⟨326981345432212524266461259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217987563621475016177640839 326981345432212524266461259)
                ·
                  refine ⟨490472018148318786399691889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 326981345432212524266461259 490472018148318786399691889)
                  ·
                    refine ⟨367854013611239089799768917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 490472018148318786399691889 367854013611239089799768917)
                    ·
                      refine ⟨2155394611003354041795521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 367854013611239089799768917 2155394611003354041795521)
                      ·
                        rfl

theorem cell23_4197616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_4197616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197616 prefixEnd_4197616 := by exact prefixLift 4197616
  have htrace : WordTrace (prefixWord ++ tailWord_4197616) baseStart_4197616 baseEnd_4197616 := by
    simpa [prefixWord, tailWord_4197616, baseEnd_4197616] using wordTrace_append hprefix tailTrace_4197616
  have hstable : (prefixWord ++ tailWord_4197616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197616).length < 2 ^ (prefixWord ++ tailWord_4197616).sum := by decide
  have hdescent : baseEnd_4197616 < baseStart_4197616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197623 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 5, 4]
def baseStart_4197623 : Nat := 118140960795 + 4197623 * 2 ^ 59
def prefixEnd_4197623 : Nat := 4983230072969 + 3 ^ 40 * 4197623 * 2
def baseEnd_4197623 : Nat := 718466068455978504802663

theorem tailTrace_4197623 : CollatzResearch.WordTrace tailWord_4197623 prefixEnd_4197623 718466068455978504802663 := by
  unfold tailWord_4197623
  simp only [CollatzResearch.WordTrace]
  refine ⟨153099888471736242778429523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102066592314490828518953015 153099888471736242778429523)
  ·
    refine ⟨229649832707604364167644285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153099888471736242778429523 229649832707604364167644285)
    ·
      refine ⟨86118687265351636562866607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229649832707604364167644285 86118687265351636562866607)
      ·
        refine ⟨129178030898027454844299911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86118687265351636562866607 129178030898027454844299911)
        ·
          refine ⟨193767046347041182266449867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129178030898027454844299911 193767046347041182266449867)
          ·
            refine ⟨290650569520561773399674801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193767046347041182266449867 290650569520561773399674801)
            ·
              refine ⟨217987927140421330049756101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290650569520561773399674801 217987927140421330049756101)
              ·
                refine ⟨40872736338828999384329269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217987927140421330049756101 40872736338828999384329269)
                ·
                  refine ⟨3831819031765218692280869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40872736338828999384329269 3831819031765218692280869)
                  ·
                    refine ⟨718466068455978504802663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3831819031765218692280869 718466068455978504802663)
                    ·
                      rfl

theorem cell23_4197623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5, 4].length) (baseStart_4197623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197623 prefixEnd_4197623 := by exact prefixLift 4197623
  have htrace : WordTrace (prefixWord ++ tailWord_4197623) baseStart_4197623 baseEnd_4197623 := by
    simpa [prefixWord, tailWord_4197623, baseEnd_4197623] using wordTrace_append hprefix tailTrace_4197623
  have hstable : (prefixWord ++ tailWord_4197623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197623).length < 2 ^ (prefixWord ++ tailWord_4197623).sum := by decide
  have hdescent : baseEnd_4197623 < baseStart_4197623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197664 : List Nat := [2, 1, 1, 5, 4, 1, 1, 1, 2, 1, 4]
def baseStart_4197664 : Nat := 118140960795 + 4197664 * 2 ^ 59
def prefixEnd_4197664 : Nat := 4983230072969 + 3 ^ 40 * 4197664 * 2
def baseEnd_4197664 : Nat := 2155419258074769853995301

theorem tailTrace_4197664 : CollatzResearch.WordTrace tailWord_4197664 prefixEnd_4197664 2155419258074769853995301 := by
  unfold tailWord_4197664
  simp only [CollatzResearch.WordTrace]
  refine ⟨76550691932293853390336023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102067589243058471187114697 76550691932293853390336023)
  ·
    refine ⟨114826037898440780085504035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76550691932293853390336023 114826037898440780085504035)
    ·
      refine ⟨172239056847661170128256053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114826037898440780085504035 172239056847661170128256053)
      ·
        refine ⟨16147411579468234699524005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 172239056847661170128256053 16147411579468234699524005)
        ·
          refine ⟨3027639671150294006160751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16147411579468234699524005 3027639671150294006160751)
          ·
            refine ⟨4541459506725441009241127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3027639671150294006160751 4541459506725441009241127)
            ·
              refine ⟨6812189260088161513861691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4541459506725441009241127 6812189260088161513861691)
              ·
                refine ⟨10218283890132242270792537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6812189260088161513861691 10218283890132242270792537)
                ·
                  refine ⟨7663712917599181703094403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10218283890132242270792537 7663712917599181703094403)
                  ·
                    refine ⟨11495569376398772554641605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7663712917599181703094403 11495569376398772554641605)
                    ·
                      refine ⟨2155419258074769853995301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11495569376398772554641605 2155419258074769853995301)
                      ·
                        rfl

theorem cell23_4197664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_4197664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197664 prefixEnd_4197664 := by exact prefixLift 4197664
  have htrace : WordTrace (prefixWord ++ tailWord_4197664) baseStart_4197664 baseEnd_4197664 := by
    simpa [prefixWord, tailWord_4197664, baseEnd_4197664] using wordTrace_append hprefix tailTrace_4197664
  have hstable : (prefixWord ++ tailWord_4197664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197664).length < 2 ^ (prefixWord ++ tailWord_4197664).sum := by decide
  have hdescent : baseEnd_4197664 < baseStart_4197664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197667 : List Nat := [1, 1, 1, 4, 2, 5, 1, 1, 2, 2, 3]
def baseStart_4197667 : Nat := 118140960795 + 4197667 * 2 ^ 59
def prefixEnd_4197667 : Nat := 4983230072969 + 3 ^ 40 * 4197667 * 2
def baseEnd_4197667 : Nat := 2155420798516733342257787

theorem tailTrace_4197667 : CollatzResearch.WordTrace tailWord_4197667 prefixEnd_4197667 2155420798516733342257787 := by
  unfold tailWord_4197667
  simp only [CollatzResearch.WordTrace]
  refine ⟨153101493283576838293031255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102067662189051225528687503 153101493283576838293031255)
  ·
    refine ⟨229652239925365257439546883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153101493283576838293031255 229652239925365257439546883)
    ·
      refine ⟨344478359888047886159320325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229652239925365257439546883 344478359888047886159320325)
      ·
        refine ⟨64589692479008978654872561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 344478359888047886159320325 64589692479008978654872561)
        ·
          refine ⟨48442269359256733991154421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64589692479008978654872561 48442269359256733991154421)
          ·
            refine ⟨4541462752430318811670727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48442269359256733991154421 4541462752430318811670727)
            ·
              refine ⟨6812194128645478217506091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4541462752430318811670727 6812194128645478217506091)
              ·
                refine ⟨10218291192968217326259137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6812194128645478217506091 10218291192968217326259137)
                ·
                  refine ⟨7663718394726162994694353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10218291192968217326259137 7663718394726162994694353)
                  ·
                    refine ⟨5747788796044622246020765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7663718394726162994694353 5747788796044622246020765)
                    ·
                      refine ⟨2155420798516733342257787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5747788796044622246020765 2155420798516733342257787)
                      ·
                        rfl

theorem cell23_4197667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_4197667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197667 prefixEnd_4197667 := by exact prefixLift 4197667
  have htrace : WordTrace (prefixWord ++ tailWord_4197667) baseStart_4197667 baseEnd_4197667 := by
    simpa [prefixWord, tailWord_4197667, baseEnd_4197667] using wordTrace_append hprefix tailTrace_4197667
  have hstable : (prefixWord ++ tailWord_4197667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197667).length < 2 ^ (prefixWord ++ tailWord_4197667).sum := by decide
  have hdescent : baseEnd_4197667 < baseStart_4197667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197674 : List Nat := [3, 1, 4, 2, 1, 1, 1, 5, 1, 4]
def baseStart_4197674 : Nat := 118140960795 + 4197674 * 2 ^ 59
def prefixEnd_4197674 : Nat := 4983230072969 + 3 ^ 40 * 4197674 * 2
def baseEnd_4197674 : Nat := 718474797627104938290085

theorem tailTrace_4197674 : CollatzResearch.WordTrace tailWord_4197674 prefixEnd_4197674 718474797627104938290085 := by
  unfold tailWord_4197674
  simp only [CollatzResearch.WordTrace]
  refine ⟨38275437148637869622134019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102067832396367652325690717 38275437148637869622134019)
  ·
    refine ⟨57413155722956804433201029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38275437148637869622134019 57413155722956804433201029)
    ·
      refine ⟨10764966698054400831225193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57413155722956804433201029 10764966698054400831225193)
      ·
        refine ⟨8073725023540800623418895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10764966698054400831225193 8073725023540800623418895)
        ·
          refine ⟨12110587535311200935128343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8073725023540800623418895 12110587535311200935128343)
          ·
            refine ⟨18165881302966801402692515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12110587535311200935128343 18165881302966801402692515)
            ·
              refine ⟨27248821954450202104038773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18165881302966801402692515 27248821954450202104038773)
              ·
                refine ⟨2554577058229706447253635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27248821954450202104038773 2554577058229706447253635)
                ·
                  refine ⟨3831865587344559670880453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2554577058229706447253635 3831865587344559670880453)
                  ·
                    refine ⟨718474797627104938290085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3831865587344559670880453 718474797627104938290085)
                    ·
                      rfl

theorem cell23_4197674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_4197674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197674 prefixEnd_4197674 := by exact prefixLift 4197674
  have htrace : WordTrace (prefixWord ++ tailWord_4197674) baseStart_4197674 baseEnd_4197674 := by
    simpa [prefixWord, tailWord_4197674, baseEnd_4197674] using wordTrace_append hprefix tailTrace_4197674
  have hstable : (prefixWord ++ tailWord_4197674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197674).length < 2 ^ (prefixWord ++ tailWord_4197674).sum := by decide
  have hdescent : baseEnd_4197674 < baseStart_4197674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197680 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 5, 1, 3]
def baseStart_4197680 : Nat := 118140960795 + 4197680 * 2 ^ 59
def prefixEnd_4197680 : Nat := 4983230072969 + 3 ^ 40 * 4197680 * 2
def baseEnd_4197680 : Nat := 2155427473765241791395227

theorem tailTrace_4197680 : CollatzResearch.WordTrace tailWord_4197680 prefixEnd_4197680 2155427473765241791395227 := by
  unfold tailWord_4197680
  simp only [CollatzResearch.WordTrace]
  refine ⟨76550983716264870756627247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102067978288353161008836329 76550983716264870756627247)
  ·
    refine ⟨114826475574397306134940871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76550983716264870756627247 114826475574397306134940871)
    ·
      refine ⟨172239713361595959202411307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114826475574397306134940871 172239713361595959202411307)
      ·
        refine ⟨258359570042393938803616961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172239713361595959202411307 258359570042393938803616961)
        ·
          refine ⟨193769677531795454102712721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258359570042393938803616961 193769677531795454102712721)
          ·
            refine ⟨145327258148846590577034541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193769677531795454102712721 145327258148846590577034541)
            ·
              refine ⟨54497721805817471466387953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145327258148846590577034541 54497721805817471466387953)
              ·
                refine ⟨40873291354363103599790965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54497721805817471466387953 40873291354363103599790965)
                ·
                  refine ⟨3831871064471540962480403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40873291354363103599790965 3831871064471540962480403)
                  ·
                    refine ⟨5747806596707311443720605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3831871064471540962480403 5747806596707311443720605)
                    ·
                      refine ⟨2155427473765241791395227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5747806596707311443720605 2155427473765241791395227)
                      ·
                        rfl

theorem cell23_4197680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 5, 1, 3].length) (baseStart_4197680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197680 prefixEnd_4197680 := by exact prefixLift 4197680
  have htrace : WordTrace (prefixWord ++ tailWord_4197680) baseStart_4197680 baseEnd_4197680 := by
    simpa [prefixWord, tailWord_4197680, baseEnd_4197680] using wordTrace_append hprefix tailTrace_4197680
  have hstable : (prefixWord ++ tailWord_4197680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197680).length < 2 ^ (prefixWord ++ tailWord_4197680).sum := by decide
  have hdescent : baseEnd_4197680 < baseStart_4197680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197717 : List Nat := [1, 3, 2, 2, 3, 2, 2, 2, 1, 5]
def baseStart_4197717 : Nat := 118140960795 + 4197717 * 2 ^ 59
def prefixEnd_4197717 : Nat := 4983230072969 + 3 ^ 40 * 4197717 * 2
def baseEnd_4197717 : Nat := 718482157516486048877519

theorem tailTrace_4197717 : CollatzResearch.WordTrace tailWord_4197717 prefixEnd_4197717 718482157516486048877519 := by
  unfold tailWord_4197717
  simp only [CollatzResearch.WordTrace]
  refine ⟨153103316933395696832351405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102068877955597131221567603 153103316933395696832351405)
  ·
    refine ⟨57413743850023386312131777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153103316933395696832351405 57413743850023386312131777)
    ·
      refine ⟨43060307887517539734098833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57413743850023386312131777 43060307887517539734098833)
      ·
        refine ⟨32295230915638154800574125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43060307887517539734098833 32295230915638154800574125)
        ·
          refine ⟨12110711593364308050215297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32295230915638154800574125 12110711593364308050215297)
          ·
            refine ⟨9083033695023231037661473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12110711593364308050215297 9083033695023231037661473)
            ·
              refine ⟨6812275271267423278246105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9083033695023231037661473 6812275271267423278246105)
              ·
                refine ⟨5109206453450567458684579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6812275271267423278246105 5109206453450567458684579)
                ·
                  refine ⟨7663809680175851188026869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5109206453450567458684579 7663809680175851188026869)
                  ·
                    refine ⟨718482157516486048877519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7663809680175851188026869 718482157516486048877519)
                    ·
                      rfl

theorem cell23_4197717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_4197717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197717 prefixEnd_4197717 := by exact prefixLift 4197717
  have htrace : WordTrace (prefixWord ++ tailWord_4197717) baseStart_4197717 baseEnd_4197717 := by
    simpa [prefixWord, tailWord_4197717, baseEnd_4197717] using wordTrace_append hprefix tailTrace_4197717
  have hstable : (prefixWord ++ tailWord_4197717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197717).length < 2 ^ (prefixWord ++ tailWord_4197717).sum := by decide
  have hdescent : baseEnd_4197717 < baseStart_4197717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197720 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 2, 6, 2]
def baseStart_4197720 : Nat := 118140960795 + 4197720 * 2 ^ 59
def prefixEnd_4197720 : Nat := 4983230072969 + 3 ^ 40 * 4197720 * 2
def baseEnd_4197720 : Nat := 2155448012991421634895043

theorem tailTrace_4197720 : CollatzResearch.WordTrace tailWord_4197720 prefixEnd_4197720 2155448012991421634895043 := by
  unfold tailWord_4197720
  simp only [CollatzResearch.WordTrace]
  refine ⟨76551713176192414172355307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102068950901589885563140409 76551713176192414172355307)
  ·
    refine ⟨114827569764288621258532961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76551713176192414172355307 114827569764288621258532961)
    ·
      refine ⟨86120677323216465943899721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114827569764288621258532961 86120677323216465943899721)
      ·
        refine ⟨64590507992412349457924791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86120677323216465943899721 64590507992412349457924791)
        ·
          refine ⟨96885761988618524186887187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64590507992412349457924791 96885761988618524186887187)
          ·
            refine ⟨145328642982927786280330781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96885761988618524186887187 145328642982927786280330781)
            ·
              refine ⟨54498241118597919855124043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145328642982927786280330781 54498241118597919855124043)
              ·
                refine ⟨81747361677896879782686065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54498241118597919855124043 81747361677896879782686065)
                ·
                  refine ⟨61310521258422659837014549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81747361677896879782686065 61310521258422659837014549)
                  ·
                    refine ⟨2873930683988562179860057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61310521258422659837014549 2873930683988562179860057)
                    ·
                      refine ⟨2155448012991421634895043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2873930683988562179860057 2155448012991421634895043)
                      ·
                        rfl

theorem cell23_4197720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 6, 2].length) (baseStart_4197720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197720 prefixEnd_4197720 := by exact prefixLift 4197720
  have htrace : WordTrace (prefixWord ++ tailWord_4197720) baseStart_4197720 baseEnd_4197720 := by
    simpa [prefixWord, tailWord_4197720, baseEnd_4197720] using wordTrace_append hprefix tailTrace_4197720
  have hstable : (prefixWord ++ tailWord_4197720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197720).length < 2 ^ (prefixWord ++ tailWord_4197720).sum := by decide
  have hdescent : baseEnd_4197720 < baseStart_4197720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197725 : List Nat := [1, 4, 5, 1, 1, 2, 1, 3, 1, 4]
def baseStart_4197725 : Nat := 118140960795 + 4197725 * 2 ^ 59
def prefixEnd_4197725 : Nat := 4983230072969 + 3 ^ 40 * 4197725 * 2
def baseEnd_4197725 : Nat := 718483526798231371777507

theorem tailTrace_4197725 : CollatzResearch.WordTrace tailWord_4197725 prefixEnd_4197725 718483526798231371777507 := by
  unfold tailWord_4197725
  simp only [CollatzResearch.WordTrace]
  refine ⟨153103608717366714198642629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102069072478244476132428419 153103608717366714198642629)
  ·
    refine ⟨28706926634506258912245493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153103608717366714198642629 28706926634506258912245493)
    ·
      refine ⟨2691274371984961773023015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28706926634506258912245493 2691274371984961773023015)
      ·
        refine ⟨4036911557977442659534523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2691274371984961773023015 4036911557977442659534523)
        ·
          refine ⟨6055367336966163989301785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4036911557977442659534523 6055367336966163989301785)
          ·
            refine ⟨4541525502724622991976339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6055367336966163989301785 4541525502724622991976339)
            ·
              refine ⟨6812288254086934487964509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4541525502724622991976339 6812288254086934487964509)
              ·
                refine ⟨2554608095282600432986691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6812288254086934487964509 2554608095282600432986691)
                ·
                  refine ⟨3831912142923900649480037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2554608095282600432986691 3831912142923900649480037)
                  ·
                    refine ⟨718483526798231371777507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3831912142923900649480037 718483526798231371777507)
                    ·
                      rfl

theorem cell23_4197725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_4197725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197725 prefixEnd_4197725 := by exact prefixLift 4197725
  have htrace : WordTrace (prefixWord ++ tailWord_4197725) baseStart_4197725 baseEnd_4197725 := by
    simpa [prefixWord, tailWord_4197725, baseEnd_4197725] using wordTrace_append hprefix tailTrace_4197725
  have hstable : (prefixWord ++ tailWord_4197725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197725).length < 2 ^ (prefixWord ++ tailWord_4197725).sum := by decide
  have hdescent : baseEnd_4197725 < baseStart_4197725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197730 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 3, 6]
def baseStart_4197730 : Nat := 118140960795 + 4197730 * 2 ^ 59
def prefixEnd_4197730 : Nat := 4983230072969 + 3 ^ 40 * 4197730 * 2
def baseEnd_4197730 : Nat := 718484382599322198589999

theorem tailTrace_4197730 : CollatzResearch.WordTrace tailWord_4197730 prefixEnd_4197730 718484382599322198589999 := by
  unfold tailWord_4197730
  simp only [CollatzResearch.WordTrace]
  refine ⟨38275947770587150013143661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102069194054899066701716429 38275947770587150013143661)
  ·
    refine ⟨14353480413970181254928873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38275947770587150013143661 14353480413970181254928873)
    ·
      refine ⟨10765110310477635941196655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14353480413970181254928873 10765110310477635941196655)
      ·
        refine ⟨16147665465716453911794983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10765110310477635941196655 16147665465716453911794983)
        ·
          refine ⟨24221498198574680867692475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16147665465716453911794983 24221498198574680867692475)
          ·
            refine ⟨36332247297862021301538713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24221498198574680867692475 36332247297862021301538713)
            ·
              refine ⟨27249185473396515976154035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36332247297862021301538713 27249185473396515976154035)
              ·
                refine ⟨40873778210094773964231053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27249185473396515976154035 40873778210094773964231053)
                ·
                  refine ⟨15327666828785540236586645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40873778210094773964231053 15327666828785540236586645)
                  ·
                    refine ⟨718484382599322198589999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15327666828785540236586645 718484382599322198589999)
                    ·
                      rfl

theorem cell23_4197730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_4197730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197730 prefixEnd_4197730 := by exact prefixLift 4197730
  have htrace : WordTrace (prefixWord ++ tailWord_4197730) baseStart_4197730 baseEnd_4197730 := by
    simpa [prefixWord, tailWord_4197730, baseEnd_4197730] using wordTrace_append hprefix tailTrace_4197730
  have hstable : (prefixWord ++ tailWord_4197730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197730).length < 2 ^ (prefixWord ++ tailWord_4197730).sum := by decide
  have hdescent : baseEnd_4197730 < baseStart_4197730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197731 : List Nat := [1, 1, 1, 5, 2, 4, 1, 3, 1, 1, 3]
def baseStart_4197731 : Nat := 118140960795 + 4197731 * 2 ^ 59
def prefixEnd_4197731 : Nat := 4983230072969 + 3 ^ 40 * 4197731 * 2
def baseEnd_4197731 : Nat := 2155453661278621091857493

theorem tailTrace_4197731 : CollatzResearch.WordTrace tailWord_4197731 prefixEnd_4197731 2155453661278621091857493 := by
  unfold tailWord_4197731
  simp only [CollatzResearch.WordTrace]
  refine ⟨153103827555344977223361047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102069218370229984815574031 153103827555344977223361047)
  ·
    refine ⟨229655741333017465835041571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153103827555344977223361047 229655741333017465835041571)
    ·
      refine ⟨344483611999526198752562357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229655741333017465835041571 344483611999526198752562357)
      ·
        refine ⟨32295338624955581133052721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 344483611999526198752562357 32295338624955581133052721)
        ·
          refine ⟨24221503968716685849789541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32295338624955581133052721 24221503968716685849789541)
          ·
            refine ⟨4541531994134378596835539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24221503968716685849789541 4541531994134378596835539)
            ·
              refine ⟨6812297991201567895253309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4541531994134378596835539 6812297991201567895253309)
              ·
                refine ⟨2554611746700587960719991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6812297991201567895253309 2554611746700587960719991)
                ·
                  refine ⟨3831917620050881941079987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2554611746700587960719991 3831917620050881941079987)
                  ·
                    refine ⟨5747876430076322911619981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3831917620050881941079987 5747876430076322911619981)
                    ·
                      refine ⟨2155453661278621091857493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5747876430076322911619981 2155453661278621091857493)
                      ·
                        rfl

theorem cell23_4197731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_4197731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197731 prefixEnd_4197731 := by exact prefixLift 4197731
  have htrace : WordTrace (prefixWord ++ tailWord_4197731) baseStart_4197731 baseEnd_4197731 := by
    simpa [prefixWord, tailWord_4197731, baseEnd_4197731] using wordTrace_append hprefix tailTrace_4197731
  have hstable : (prefixWord ++ tailWord_4197731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197731).length < 2 ^ (prefixWord ++ tailWord_4197731).sum := by decide
  have hdescent : baseEnd_4197731 < baseStart_4197731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197740 : List Nat := [2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 5]
def baseStart_4197740 : Nat := 118140960795 + 4197740 * 2 ^ 59
def prefixEnd_4197740 : Nat := 4983230072969 + 3 ^ 40 * 4197740 * 2
def baseEnd_4197740 : Nat := 2155458282604511556644951

theorem tailTrace_4197740 : CollatzResearch.WordTrace tailWord_4197740 prefixEnd_4197740 2155458282604511556644951 := by
  unfold tailWord_4197740
  simp only [CollatzResearch.WordTrace]
  refine ⟨76552077906156185880219337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102069437208208247840292449 76552077906156185880219337)
  ·
    refine ⟨57414058429617139410164503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76552077906156185880219337 57414058429617139410164503)
    ·
      refine ⟨86121087644425709115246755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57414058429617139410164503 86121087644425709115246755)
      ·
        refine ⟨129181631466638563672870133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86121087644425709115246755 129181631466638563672870133)
        ·
          refine ⟨12110777949997365344331575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 129181631466638563672870133 12110777949997365344331575)
          ·
            refine ⟨18166166924996048016497363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12110777949997365344331575 18166166924996048016497363)
            ·
              refine ⟨27249250387494072024746045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18166166924996048016497363 27249250387494072024746045)
              ·
                refine ⟨10218468895310277009279767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27249250387494072024746045 10218468895310277009279767)
                ·
                  refine ⟨15327703342965415513919651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10218468895310277009279767 15327703342965415513919651)
                  ·
                    refine ⟨22991555014448123270879477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15327703342965415513919651 22991555014448123270879477)
                    ·
                      refine ⟨2155458282604511556644951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22991555014448123270879477 2155458282604511556644951)
                      ·
                        rfl

theorem cell23_4197740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_4197740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197740 prefixEnd_4197740 := by exact prefixLift 4197740
  have htrace : WordTrace (prefixWord ++ tailWord_4197740) baseStart_4197740 baseEnd_4197740 := by
    simpa [prefixWord, tailWord_4197740, baseEnd_4197740] using wordTrace_append hprefix tailTrace_4197740
  have hstable : (prefixWord ++ tailWord_4197740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197740).length < 2 ^ (prefixWord ++ tailWord_4197740).sum := by decide
  have hdescent : baseEnd_4197740 < baseStart_4197740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197764 : List Nat := [2, 3, 2, 1, 1, 3, 4, 1, 2, 4]
def baseStart_4197764 : Nat := 118140960795 + 4197764 * 2 ^ 59
def prefixEnd_4197764 : Nat := 4983230072969 + 3 ^ 40 * 4197764 * 2
def baseEnd_4197764 : Nat := 718490202046739820914947

theorem tailTrace_4197764 : CollatzResearch.WordTrace tailWord_4197764 prefixEnd_4197764 718490202046739820914947 := by
  unfold tailWord_4197764
  simp only [CollatzResearch.WordTrace]
  refine ⟨76552515582112711929656173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102070020776150282572874897 76552515582112711929656173)
  ·
    refine ⟨28707193343292266973621065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76552515582112711929656173 28707193343292266973621065)
    ·
      refine ⟨21530395007469200230215799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28707193343292266973621065 21530395007469200230215799)
      ·
        refine ⟨32295592511203800345323699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21530395007469200230215799 32295592511203800345323699)
        ·
          refine ⟨48443388766805700517985549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32295592511203800345323699 48443388766805700517985549)
          ·
            refine ⟨18166270787552137694244581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48443388766805700517985549 18166270787552137694244581)
            ·
              refine ⟨3406175772666025817670859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18166270787552137694244581 3406175772666025817670859)
              ·
                refine ⟨5109263658999038726506289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3406175772666025817670859 5109263658999038726506289)
                ·
                  refine ⟨3831947744249279044879717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5109263658999038726506289 3831947744249279044879717)
                  ·
                    refine ⟨718490202046739820914947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3831947744249279044879717 718490202046739820914947)
                    ·
                      rfl

theorem cell23_4197764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_4197764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197764 prefixEnd_4197764 := by exact prefixLift 4197764
  have htrace : WordTrace (prefixWord ++ tailWord_4197764) baseStart_4197764 baseEnd_4197764 := by
    simpa [prefixWord, tailWord_4197764, baseEnd_4197764] using wordTrace_append hprefix tailTrace_4197764
  have hstable : (prefixWord ++ tailWord_4197764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197764).length < 2 ^ (prefixWord ++ tailWord_4197764).sum := by decide
  have hdescent : baseEnd_4197764 < baseStart_4197764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197774 : List Nat := [4, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3]
def baseStart_4197774 : Nat := 118140960795 + 4197774 * 2 ^ 59
def prefixEnd_4197774 : Nat := 4983230072969 + 3 ^ 40 * 4197774 * 2
def baseEnd_4197774 : Nat := 2155475740946764423619795

theorem tailTrace_4197774 : CollatzResearch.WordTrace tailWord_4197774 prefixEnd_4197774 2155475740946764423619795 := by
  unfold tailWord_4197774
  simp only [CollatzResearch.WordTrace]
  refine ⟨19138174486773649445897047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102070263929459463711450917 19138174486773649445897047)
  ·
    refine ⟨28707261730160474168845571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19138174486773649445897047 28707261730160474168845571)
    ·
      refine ⟨43060892595240711253268357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28707261730160474168845571 43060892595240711253268357)
      ·
        refine ⟨8073917361607633359987817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43060892595240711253268357 8073917361607633359987817)
        ·
          refine ⟨6055438021205725019990863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8073917361607633359987817 6055438021205725019990863)
          ·
            refine ⟨9083157031808587529986295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6055438021205725019990863 9083157031808587529986295)
            ·
              refine ⟨13624735547712881294979443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9083157031808587529986295 13624735547712881294979443)
              ·
                refine ⟨20437103321569321942469165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13624735547712881294979443 20437103321569321942469165)
                ·
                  refine ⟨7663913745588495728425937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20437103321569321942469165 7663913745588495728425937)
                  ·
                    refine ⟨5747935309191371796319453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7663913745588495728425937 5747935309191371796319453)
                    ·
                      refine ⟨2155475740946764423619795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5747935309191371796319453 2155475740946764423619795)
                      ·
                        rfl

theorem cell23_4197774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_4197774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197774 prefixEnd_4197774 := by exact prefixLift 4197774
  have htrace : WordTrace (prefixWord ++ tailWord_4197774) baseStart_4197774 baseEnd_4197774 := by
    simpa [prefixWord, tailWord_4197774, baseEnd_4197774] using wordTrace_append hprefix tailTrace_4197774
  have hstable : (prefixWord ++ tailWord_4197774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197774).length < 2 ^ (prefixWord ++ tailWord_4197774).sum := by decide
  have hdescent : baseEnd_4197774 < baseStart_4197774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197805 : List Nat := [1, 5, 2, 2, 1, 1, 4, 2, 1, 2, 2]
def baseStart_4197805 : Nat := 118140960795 + 4197805 * 2 ^ 59
def prefixEnd_4197805 : Nat := 4983230072969 + 3 ^ 40 * 4197805 * 2
def baseEnd_4197805 : Nat := 2155491658847053802332153

theorem tailTrace_4197805 : CollatzResearch.WordTrace tailWord_4197805 prefixEnd_4197805 2155491658847053802332153 := by
  unfold tailWord_4197805
  simp only [CollatzResearch.WordTrace]
  refine ⟨153106526557076887861554869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102071017704717925241036579 153106526557076887861554869)
  ·
    refine ⟨14353736864725958237020769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 153106526557076887861554869 14353736864725958237020769)
    ·
      refine ⟨10765302648544468677765577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14353736864725958237020769 10765302648544468677765577)
      ·
        refine ⟨8073976986408351508324183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10765302648544468677765577 8073976986408351508324183)
        ·
          refine ⟨12110965479612527262486275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8073976986408351508324183 12110965479612527262486275)
          ·
            refine ⟨18166448219418790893729413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12110965479612527262486275 18166448219418790893729413)
            ·
              refine ⟨3406209041141023292574265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18166448219418790893729413 3406209041141023292574265)
              ·
                refine ⟨2554656780855767469430699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3406209041141023292574265 2554656780855767469430699)
                ·
                  refine ⟨3831985171283651204146049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2554656780855767469430699 3831985171283651204146049)
                  ·
                    refine ⟨2873988878462738403109537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3831985171283651204146049 2873988878462738403109537)
                    ·
                      refine ⟨2155491658847053802332153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2873988878462738403109537 2155491658847053802332153)
                      ·
                        rfl

theorem cell23_4197805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_4197805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197805 prefixEnd_4197805 := by exact prefixLift 4197805
  have htrace : WordTrace (prefixWord ++ tailWord_4197805) baseStart_4197805 baseEnd_4197805 := by
    simpa [prefixWord, tailWord_4197805, baseEnd_4197805] using wordTrace_append hprefix tailTrace_4197805
  have hstable : (prefixWord ++ tailWord_4197805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197805).length < 2 ^ (prefixWord ++ tailWord_4197805).sum := by decide
  have hdescent : baseEnd_4197805 < baseStart_4197805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197827 : List Nat := [1, 1, 1, 3, 1, 1, 5, 3, 1, 4, 2]
def baseStart_4197827 : Nat := 118140960795 + 4197827 * 2 ^ 59
def prefixEnd_4197827 : Nat := 4983230072969 + 3 ^ 40 * 4197827 * 2
def baseEnd_4197827 : Nat := 2155502955421452716257051

theorem tailTrace_4197827 : CollatzResearch.WordTrace tailWord_4197827 prefixEnd_4197827 2155502955421452716257051 := by
  unfold tailWord_4197827
  simp only [CollatzResearch.WordTrace]
  refine ⟨153107328962997185618855735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102071552641998123745903823 153107328962997185618855735)
  ·
    refine ⟨229660993444495778428283603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153107328962997185618855735 229660993444495778428283603)
    ·
      refine ⟨344491490166743667642425405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229660993444495778428283603 344491490166743667642425405)
      ·
        refine ⟨129184308812528875365909527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 344491490166743667642425405 129184308812528875365909527)
        ·
          refine ⟨193776463218793313048864291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129184308812528875365909527 193776463218793313048864291)
          ·
            refine ⟨290664694828189969573296437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193776463218793313048864291 290664694828189969573296437)
            ·
              refine ⟨27249815140142809647496541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 290664694828189969573296437 27249815140142809647496541)
              ·
                refine ⟨10218680677553553617811203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27249815140142809647496541 10218680677553553617811203)
                ·
                  refine ⟨15328021016330330426716805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10218680677553553617811203 15328021016330330426716805)
                  ·
                    refine ⟨2874003940561936955009401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15328021016330330426716805 2874003940561936955009401)
                    ·
                      refine ⟨2155502955421452716257051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2874003940561936955009401 2155502955421452716257051)
                      ·
                        rfl

theorem cell23_4197827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 4, 2].length) (baseStart_4197827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197827 prefixEnd_4197827 := by exact prefixLift 4197827
  have htrace : WordTrace (prefixWord ++ tailWord_4197827) baseStart_4197827 baseEnd_4197827 := by
    simpa [prefixWord, tailWord_4197827, baseEnd_4197827] using wordTrace_append hprefix tailTrace_4197827
  have hstable : (prefixWord ++ tailWord_4197827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197827).length < 2 ^ (prefixWord ++ tailWord_4197827).sum := by decide
  have hdescent : baseEnd_4197827 < baseStart_4197827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197861 : List Nat := [1, 3, 1, 5, 1, 2, 1, 1, 4, 2, 2]
def baseStart_4197861 : Nat := 118140960795 + 4197861 * 2 ^ 59
def prefixEnd_4197861 : Nat := 4983230072969 + 3 ^ 40 * 4197861 * 2
def baseEnd_4197861 : Nat := 2155520413763705583231895

theorem tailTrace_4197861 : CollatzResearch.WordTrace tailWord_4197861 prefixEnd_4197861 2155520413763705583231895 := by
  unfold tailWord_4197861
  simp only [CollatzResearch.WordTrace]
  refine ⟨153108569044874009425593437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102072379363249339617062291 153108569044874009425593437)
  ·
    refine ⟨57415713391827753534597539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153108569044874009425593437 57415713391827753534597539)
    ·
      refine ⟨86123570087741630301896309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57415713391827753534597539 86123570087741630301896309)
      ·
        refine ⟨8074084695725777840802779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86123570087741630301896309 8074084695725777840802779)
        ·
          refine ⟨12111127043588666761204169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8074084695725777840802779 12111127043588666761204169)
          ·
            refine ⟨9083345282691500070903127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12111127043588666761204169 9083345282691500070903127)
            ·
              refine ⟨13625017924037250106354691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9083345282691500070903127 13625017924037250106354691)
              ·
                refine ⟨20437526886055875159532037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13625017924037250106354691 20437526886055875159532037)
                ·
                  refine ⟨3832036291135476592412257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20437526886055875159532037 3832036291135476592412257)
                  ·
                    refine ⟨2874027218351607444309193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3832036291135476592412257 2874027218351607444309193)
                    ·
                      refine ⟨2155520413763705583231895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2874027218351607444309193 2155520413763705583231895)
                      ·
                        rfl

theorem cell23_4197861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_4197861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197861 prefixEnd_4197861 := by exact prefixLift 4197861
  have htrace : WordTrace (prefixWord ++ tailWord_4197861) baseStart_4197861 baseEnd_4197861 := by
    simpa [prefixWord, tailWord_4197861, baseEnd_4197861] using wordTrace_append hprefix tailTrace_4197861
  have hstable : (prefixWord ++ tailWord_4197861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197861).length < 2 ^ (prefixWord ++ tailWord_4197861).sum := by decide
  have hdescent : baseEnd_4197861 < baseStart_4197861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197880 : List Nat := [2, 1, 2, 1, 1, 5, 1, 2, 1, 7]
def baseStart_4197880 : Nat := 118140960795 + 4197880 * 2 ^ 59
def prefixEnd_4197880 : Nat := 4983230072969 + 3 ^ 40 * 4197880 * 2
def baseEnd_4197880 : Nat := 718510056632047002964769

theorem tailTrace_4197880 : CollatzResearch.WordTrace tailWord_4197880 prefixEnd_4197880 718510056632047002964769 := by
  unfold tailWord_4197880
  simp only [CollatzResearch.WordTrace]
  refine ⟨76554631015902587835267547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102072841354536783780356729 76554631015902587835267547)
  ·
    refine ⟨114831946523853881752901321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76554631015902587835267547 114831946523853881752901321)
    ·
      refine ⟨86123959892890411314675991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114831946523853881752901321 86123959892890411314675991)
      ·
        refine ⟨129185939839335616972013987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86123959892890411314675991 129185939839335616972013987)
        ·
          refine ⟨193778909759003425458020981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129185939839335616972013987 193778909759003425458020981)
          ·
            refine ⟨18166772789906571136689467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 193778909759003425458020981 18166772789906571136689467)
            ·
              refine ⟨27250159184859856705034201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18166772789906571136689467 27250159184859856705034201)
              ·
                refine ⟨20437619388644892528775651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27250159184859856705034201 20437619388644892528775651)
                ·
                  refine ⟨30656429082967338793163477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20437619388644892528775651 30656429082967338793163477)
                  ·
                    refine ⟨718510056632047002964769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30656429082967338793163477 718510056632047002964769)
                    ·
                      rfl

theorem cell23_4197880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 1, 7].length) (baseStart_4197880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197880 prefixEnd_4197880 := by exact prefixLift 4197880
  have htrace : WordTrace (prefixWord ++ tailWord_4197880) baseStart_4197880 baseEnd_4197880 := by
    simpa [prefixWord, tailWord_4197880, baseEnd_4197880] using wordTrace_append hprefix tailTrace_4197880
  have hstable : (prefixWord ++ tailWord_4197880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197880).length < 2 ^ (prefixWord ++ tailWord_4197880).sum := by decide
  have hdescent : baseEnd_4197880 < baseStart_4197880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197937 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 6, 2, 3]
def baseStart_4197937 : Nat := 118140960795 + 4197937 * 2 ^ 59
def prefixEnd_4197937 : Nat := 4983230072969 + 3 ^ 40 * 4197937 * 2
def baseEnd_4197937 : Nat := 2155559438293447285881545

theorem tailTrace_4197937 : CollatzResearch.WordTrace tailWord_4197937 prefixEnd_4197937 2155559438293447285881545 := by
  unfold tailWord_4197937
  simp only [CollatzResearch.WordTrace]
  refine ⟨153111340992598674405360065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102074227328399116270240043 153111340992598674405360065)
  ·
    refine ⟨114833505744449005804020049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153111340992598674405360065 114833505744449005804020049)
    ·
      refine ⟨86125129308336754353015037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114833505744449005804020049 86125129308336754353015037)
      ·
        refine ⟨32296923490626282882380639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86125129308336754353015037 32296923490626282882380639)
        ·
          refine ⟨48445385235939424323570959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32296923490626282882380639 48445385235939424323570959)
          ·
            refine ⟨72668077853909136485356439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48445385235939424323570959 72668077853909136485356439)
            ·
              refine ⟨109002116780863704728034659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72668077853909136485356439 109002116780863704728034659)
              ·
                refine ⟨163503175171295557092051989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109002116780863704728034659 163503175171295557092051989)
                ·
                  refine ⟨7664211336154479238689937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 163503175171295557092051989 7664211336154479238689937)
                  ·
                    refine ⟨5748158502115859429017453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7664211336154479238689937 5748158502115859429017453)
                    ·
                      refine ⟨2155559438293447285881545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5748158502115859429017453 2155559438293447285881545)
                      ·
                        rfl

theorem cell23_4197937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_4197937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197937 prefixEnd_4197937 := by exact prefixLift 4197937
  have htrace : WordTrace (prefixWord ++ tailWord_4197937) baseStart_4197937 baseEnd_4197937 := by
    simpa [prefixWord, tailWord_4197937, baseEnd_4197937] using wordTrace_append hprefix tailTrace_4197937
  have hstable : (prefixWord ++ tailWord_4197937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197937).length < 2 ^ (prefixWord ++ tailWord_4197937).sum := by decide
  have hdescent : baseEnd_4197937 < baseStart_4197937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197960 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 3, 1, 8]
def baseStart_4197960 : Nat := 118140960795 + 4197960 * 2 ^ 59
def prefixEnd_4197960 : Nat := 4983230072969 + 3 ^ 40 * 4197960 * 2
def baseEnd_4197960 : Nat := 2155571248348500695893939

theorem tailTrace_4197960 : CollatzResearch.WordTrace tailWord_4197960 prefixEnd_4197960 2155571248348500695893939 := by
  unfold tailWord_4197960
  simp only [CollatzResearch.WordTrace]
  refine ⟨76556089935757674666723667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102074786581010232888964889 76556089935757674666723667)
  ·
    refine ⟨114834134903636512000085501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76556089935757674666723667 114834134903636512000085501)
    ·
      refine ⟨43062800588863692000032063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114834134903636512000085501 43062800588863692000032063)
      ·
        refine ⟨64594200883295538000048095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43062800588863692000032063 64594200883295538000048095)
        ·
          refine ⟨96891301324943307000072143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64594200883295538000048095 96891301324943307000072143)
          ·
            refine ⟨145336951987414960500108215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96891301324943307000072143 145336951987414960500108215)
            ·
              refine ⟨218005427981122440750162323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145336951987414960500108215 218005427981122440750162323)
              ·
                refine ⟨327008141971683661125243485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218005427981122440750162323 327008141971683661125243485)
                ·
                  refine ⟨122628053239381372921966307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 327008141971683661125243485 122628053239381372921966307)
                  ·
                    refine ⟨183942079859072059382949461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 122628053239381372921966307 183942079859072059382949461)
                    ·
                      refine ⟨2155571248348500695893939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 183942079859072059382949461 2155571248348500695893939)
                      ·
                        rfl

theorem cell23_4197960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_4197960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197960 prefixEnd_4197960 := by exact prefixLift 4197960
  have htrace : WordTrace (prefixWord ++ tailWord_4197960) baseStart_4197960 baseEnd_4197960 := by
    simpa [prefixWord, tailWord_4197960, baseEnd_4197960] using wordTrace_append hprefix tailTrace_4197960
  have hstable : (prefixWord ++ tailWord_4197960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197960).length < 2 ^ (prefixWord ++ tailWord_4197960).sum := by decide
  have hdescent : baseEnd_4197960 < baseStart_4197960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197984 : List Nat := [2, 1, 1, 3, 2, 1, 1, 5, 3, 1, 3]
def baseStart_4197984 : Nat := 118140960795 + 4197984 * 2 ^ 59
def prefixEnd_4197984 : Nat := 4983230072969 + 3 ^ 40 * 4197984 * 2
def baseEnd_4197984 : Nat := 2155583571884208601993829

theorem tailTrace_4197984 : CollatzResearch.WordTrace tailWord_4197984 prefixEnd_4197984 2155583571884208601993829 := by
  unfold tailWord_4197984
  simp only [CollatzResearch.WordTrace]
  refine ⟨76556527611714200716160503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102075370148952267621547337 76556527611714200716160503)
  ·
    refine ⟨114834791417571301074240755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76556527611714200716160503 114834791417571301074240755)
    ·
      refine ⟨172252187126356951611361133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114834791417571301074240755 172252187126356951611361133)
      ·
        refine ⟨64594570172383856854260425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172252187126356951611361133 64594570172383856854260425)
        ·
          refine ⟨48445927629287892640695319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64594570172383856854260425 48445927629287892640695319)
          ·
            refine ⟨72668891443931838961042979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48445927629287892640695319 72668891443931838961042979)
            ·
              refine ⟨109003337165897758441564469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72668891443931838961042979 109003337165897758441564469)
              ·
                refine ⟨10219062859302914853896669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109003337165897758441564469 10219062859302914853896669)
                ·
                  refine ⟨3832148572238593070211251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10219062859302914853896669 3832148572238593070211251)
                  ·
                    refine ⟨5748222858357889605316877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3832148572238593070211251 5748222858357889605316877)
                    ·
                      refine ⟨2155583571884208601993829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5748222858357889605316877 2155583571884208601993829)
                      ·
                        rfl

theorem cell23_4197984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_4197984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197984 prefixEnd_4197984 := by exact prefixLift 4197984
  have htrace : WordTrace (prefixWord ++ tailWord_4197984) baseStart_4197984 baseEnd_4197984 := by
    simpa [prefixWord, tailWord_4197984, baseEnd_4197984] using wordTrace_append hprefix tailTrace_4197984
  have hstable : (prefixWord ++ tailWord_4197984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197984).length < 2 ^ (prefixWord ++ tailWord_4197984).sum := by decide
  have hdescent : baseEnd_4197984 < baseStart_4197984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4197987 : List Nat := [1, 1, 1, 5, 1, 3, 1, 2, 3, 5]
def baseStart_4197987 : Nat := 118140960795 + 4197987 * 2 ^ 59
def prefixEnd_4197987 : Nat := 4983230072969 + 3 ^ 40 * 4197987 * 2
def baseEnd_4197987 : Nat := 718528370775390696752105

theorem tailTrace_4197987 : CollatzResearch.WordTrace tailWord_4197987 prefixEnd_4197987 718528370775390696752105 := by
  unfold tailWord_4197987
  simp only [CollatzResearch.WordTrace]
  refine ⟨153113164642417532944680215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102075443094945021963120143 153113164642417532944680215)
  ·
    refine ⟨229669746963626299417020323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153113164642417532944680215 229669746963626299417020323)
    ·
      refine ⟨344504620445439449125530485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229669746963626299417020323 344504620445439449125530485)
      ·
        refine ⟨32297308166759948355518483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 344504620445439449125530485 32297308166759948355518483)
        ·
          refine ⟨48445962250139922533277725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32297308166759948355518483 48445962250139922533277725)
          ·
            refine ⟨18167235843802470949979147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48445962250139922533277725 18167235843802470949979147)
            ·
              refine ⟨27250853765703706424968721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18167235843802470949979147 27250853765703706424968721)
              ·
                refine ⟨20438140324277779818726541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27250853765703706424968721 20438140324277779818726541)
                ·
                  refine ⟨7664302621604167432022453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20438140324277779818726541 7664302621604167432022453)
                  ·
                    refine ⟨718528370775390696752105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7664302621604167432022453 718528370775390696752105)
                    ·
                      rfl

theorem cell23_4197987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 5].length) (baseStart_4197987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4197987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4197987 prefixEnd_4197987 := by exact prefixLift 4197987
  have htrace : WordTrace (prefixWord ++ tailWord_4197987) baseStart_4197987 baseEnd_4197987 := by
    simpa [prefixWord, tailWord_4197987, baseEnd_4197987] using wordTrace_append hprefix tailTrace_4197987
  have hstable : (prefixWord ++ tailWord_4197987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4197987).length < 2 ^ (prefixWord ++ tailWord_4197987).sum := by decide
  have hdescent : baseEnd_4197987 < baseStart_4197987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4197987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198027 : List Nat := [1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 5]
def baseStart_4198027 : Nat := 118140960795 + 4198027 * 2 ^ 59
def prefixEnd_4198027 : Nat := 4983230072969 + 3 ^ 40 * 4198027 * 2
def baseEnd_4198027 : Nat := 2155605651552351933756131

theorem tailTrace_4198027 : CollatzResearch.WordTrace tailWord_4198027 prefixEnd_4198027 2155605651552351933756131 := by
  unfold tailWord_4198027
  simp only [CollatzResearch.WordTrace]
  refine ⟨153114623562272619776136335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102076415708181746517424223 153114623562272619776136335)
  ·
    refine ⟨229671935343408929664204503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153114623562272619776136335 229671935343408929664204503)
    ·
      refine ⟨344507903015113394496306755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229671935343408929664204503 344507903015113394496306755)
      ·
        refine ⟨516761854522670091744460133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344507903015113394496306755 516761854522670091744460133)
        ·
          refine ⟨96892847723000642202086275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 516761854522670091744460133 96892847723000642202086275)
          ·
            refine ⟨145339271584500963303129413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96892847723000642202086275 145339271584500963303129413)
            ·
              refine ⟨27251113422093930619336765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145339271584500963303129413 27251113422093930619336765)
              ·
                refine ⟨10219167533285223982251287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27251113422093930619336765 10219167533285223982251287)
                ·
                  refine ⟨15328751299927835973376931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10219167533285223982251287 15328751299927835973376931)
                  ·
                    refine ⟨22993126949891753960065397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15328751299927835973376931 22993126949891753960065397)
                    ·
                      refine ⟨2155605651552351933756131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22993126949891753960065397 2155605651552351933756131)
                      ·
                        rfl

theorem cell23_4198027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 5].length) (baseStart_4198027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198027 prefixEnd_4198027 := by exact prefixLift 4198027
  have htrace : WordTrace (prefixWord ++ tailWord_4198027) baseStart_4198027 baseEnd_4198027 := by
    simpa [prefixWord, tailWord_4198027, baseEnd_4198027] using wordTrace_append hprefix tailTrace_4198027
  have hstable : (prefixWord ++ tailWord_4198027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198027).length < 2 ^ (prefixWord ++ tailWord_4198027).sum := by decide
  have hdescent : baseEnd_4198027 < baseStart_4198027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198037 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 3, 2, 4]
def baseStart_4198037 : Nat := 118140960795 + 4198037 * 2 ^ 59
def prefixEnd_4198037 : Nat := 4983230072969 + 3 ^ 40 * 4198037 * 2
def baseEnd_4198037 : Nat := 2155610786358896894631085

theorem tailTrace_4198037 : CollatzResearch.WordTrace tailWord_4198037 prefixEnd_4198037 2155610786358896894631085 := by
  unfold tailWord_4198037
  simp only [CollatzResearch.WordTrace]
  refine ⟨153114988292236391484000365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102076658861490927656000243 153114988292236391484000365)
  ·
    refine ⟨57418120609588646806500137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153114988292236391484000365 57418120609588646806500137)
    ·
      refine ⟨43063590457191485104875103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57418120609588646806500137 43063590457191485104875103)
      ·
        refine ⟨64595385685787227657312655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43063590457191485104875103 64595385685787227657312655)
        ·
          refine ⟨96893078528680841485968983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64595385685787227657312655 96893078528680841485968983)
          ·
            refine ⟨145339617793021262228953475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96893078528680841485968983 145339617793021262228953475)
            ·
              refine ⟨218009426689531893343430213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145339617793021262228953475 218009426689531893343430213)
              ·
                refine ⟨40876767504287230001893165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 218009426689531893343430213 40876767504287230001893165)
                ·
                  refine ⟨15328787814107711250709937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40876767504287230001893165 15328787814107711250709937)
                  ·
                    refine ⟨11496590860580783438032453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15328787814107711250709937 11496590860580783438032453)
                    ·
                      refine ⟨2155610786358896894631085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11496590860580783438032453 2155610786358896894631085)
                      ·
                        rfl

theorem cell23_4198037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_4198037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198037 prefixEnd_4198037 := by exact prefixLift 4198037
  have htrace : WordTrace (prefixWord ++ tailWord_4198037) baseStart_4198037 baseEnd_4198037 := by
    simpa [prefixWord, tailWord_4198037, baseEnd_4198037] using wordTrace_append hprefix tailTrace_4198037
  have hstable : (prefixWord ++ tailWord_4198037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198037).length < 2 ^ (prefixWord ++ tailWord_4198037).sum := by decide
  have hdescent : baseEnd_4198037 < baseStart_4198037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198051 : List Nat := [1, 1, 1, 4, 1, 1, 7, 1, 2, 4]
def baseStart_4198051 : Nat := 118140960795 + 4198051 * 2 ^ 59
def prefixEnd_4198051 : Nat := 4983230072969 + 3 ^ 40 * 4198051 * 2
def baseEnd_4198051 : Nat := 718539325029353279952007

theorem tailTrace_4198051 : CollatzResearch.WordTrace tailWord_4198051 prefixEnd_4198051 718539325029353279952007 := by
  unfold tailWord_4198051
  simp only [CollatzResearch.WordTrace]
  refine ⟨153115498914185671875010007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102076999276123781250006671 153115498914185671875010007)
  ·
    refine ⟨229673248371278507812515011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153115498914185671875010007 229673248371278507812515011)
    ·
      refine ⟨344509872556917761718772517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229673248371278507812515011 344509872556917761718772517)
      ·
        refine ⟨64595601104422080322269847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 344509872556917761718772517 64595601104422080322269847)
        ·
          refine ⟨96893401656633120483404771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64595601104422080322269847 96893401656633120483404771)
          ·
            refine ⟨145340102484949680725107157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96893401656633120483404771 145340102484949680725107157)
            ·
              refine ⟨3406408651991008141994699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 145340102484949680725107157 3406408651991008141994699)
              ·
                refine ⟨5109612977986512212992049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3406408651991008141994699 5109612977986512212992049)
                ·
                  refine ⟨3832209733489884159744037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5109612977986512212992049 3832209733489884159744037)
                  ·
                    refine ⟨718539325029353279952007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3832209733489884159744037 718539325029353279952007)
                    ·
                      rfl

theorem cell23_4198051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 2, 4].length) (baseStart_4198051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198051 prefixEnd_4198051 := by exact prefixLift 4198051
  have htrace : WordTrace (prefixWord ++ tailWord_4198051) baseStart_4198051 baseEnd_4198051 := by
    simpa [prefixWord, tailWord_4198051, baseEnd_4198051] using wordTrace_append hprefix tailTrace_4198051
  have hstable : (prefixWord ++ tailWord_4198051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198051).length < 2 ^ (prefixWord ++ tailWord_4198051).sum := by decide
  have hdescent : baseEnd_4198051 < baseStart_4198051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198087 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 5]
def baseStart_4198087 : Nat := 118140960795 + 4198087 * 2 ^ 59
def prefixEnd_4198087 : Nat := 4983230072969 + 3 ^ 40 * 4198087 * 2
def baseEnd_4198087 : Nat := 2155636460391621699005855

theorem tailTrace_4198087 : CollatzResearch.WordTrace tailWord_4198087 prefixEnd_4198087 2155636460391621699005855 := by
  unfold tailWord_4198087
  simp only [CollatzResearch.WordTrace]
  refine ⟨153116811942055250023320515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102077874628036833348880343 153116811942055250023320515)
  ·
    refine ⟨229675217913082875034980773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153116811942055250023320515 229675217913082875034980773)
    ·
      refine ⟨43064103358703039069058895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229675217913082875034980773 43064103358703039069058895)
      ·
        refine ⟨64596155038054558603588343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43064103358703039069058895 64596155038054558603588343)
        ·
          refine ⟨96894232557081837905382515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64596155038054558603588343 96894232557081837905382515)
          ·
            refine ⟨145341348835622756858073773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96894232557081837905382515 145341348835622756858073773)
            ·
              refine ⟨54503005813358533821777665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145341348835622756858073773 54503005813358533821777665)
              ·
                refine ⟨40877254360018900366333249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54503005813358533821777665 40877254360018900366333249)
                ·
                  refine ⟨30657940770014175274749937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40877254360018900366333249 30657940770014175274749937)
                  ·
                    refine ⟨22993455577510631456062453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30657940770014175274749937 22993455577510631456062453)
                    ·
                      refine ⟨2155636460391621699005855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22993455577510631456062453 2155636460391621699005855)
                      ·
                        rfl

theorem cell23_4198087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_4198087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198087 prefixEnd_4198087 := by exact prefixLift 4198087
  have htrace : WordTrace (prefixWord ++ tailWord_4198087) baseStart_4198087 baseEnd_4198087 := by
    simpa [prefixWord, tailWord_4198087, baseEnd_4198087] using wordTrace_append hprefix tailTrace_4198087
  have hstable : (prefixWord ++ tailWord_4198087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198087).length < 2 ^ (prefixWord ++ tailWord_4198087).sum := by decide
  have hdescent : baseEnd_4198087 < baseStart_4198087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198092 : List Nat := [2, 2, 1, 5, 3, 1, 1, 1, 3, 2, 2]
def baseStart_4198092 : Nat := 118140960795 + 4198092 * 2 ^ 59
def prefixEnd_4198092 : Nat := 4983230072969 + 3 ^ 40 * 4198092 * 2
def baseEnd_4198092 : Nat := 2155639027794894179443333

theorem tailTrace_4198092 : CollatzResearch.WordTrace tailWord_4198092 prefixEnd_4198092 2155639027794894179443333 := by
  unfold tailWord_4198092
  simp only [CollatzResearch.WordTrace]
  refine ⟨76558497153518567938626265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102077996204691423918168353 76558497153518567938626265)
  ·
    refine ⟨57418872865138925953969699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76558497153518567938626265 57418872865138925953969699)
    ·
      refine ⟨86128309297708388930954549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57418872865138925953969699 86128309297708388930954549)
      ·
        refine ⟨8074528996660161462276989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86128309297708388930954549 8074528996660161462276989)
        ·
          refine ⟨3027948373747560548353871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8074528996660161462276989 3027948373747560548353871)
          ·
            refine ⟨4541922560621340822530807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3027948373747560548353871 4541922560621340822530807)
            ·
              refine ⟨6812883840932011233796211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4541922560621340822530807 6812883840932011233796211)
              ·
                refine ⟨10219325761398016850694317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6812883840932011233796211 10219325761398016850694317)
                ·
                  refine ⟨3832247160524256319010369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10219325761398016850694317 3832247160524256319010369)
                  ·
                    refine ⟨2874185370393192239257777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3832247160524256319010369 2874185370393192239257777)
                    ·
                      refine ⟨2155639027794894179443333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2874185370393192239257777 2155639027794894179443333)
                      ·
                        rfl

theorem cell23_4198092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_4198092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198092 prefixEnd_4198092 := by exact prefixLift 4198092
  have htrace : WordTrace (prefixWord ++ tailWord_4198092) baseStart_4198092 baseEnd_4198092 := by
    simpa [prefixWord, tailWord_4198092, baseEnd_4198092] using wordTrace_append hprefix tailTrace_4198092
  have hstable : (prefixWord ++ tailWord_4198092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198092).length < 2 ^ (prefixWord ++ tailWord_4198092).sum := by decide
  have hdescent : baseEnd_4198092 < baseStart_4198092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198131 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 6, 2, 2]
def baseStart_4198131 : Nat := 118140960795 + 4198131 * 2 ^ 59
def prefixEnd_4198131 : Nat := 4983230072969 + 3 ^ 40 * 4198131 * 2
def baseEnd_4198131 : Nat := 2155659053540419526855653

theorem tailTrace_4198131 : CollatzResearch.WordTrace tailWord_4198131 prefixEnd_4198131 2155659053540419526855653 := by
  unfold tailWord_4198131
  simp only [CollatzResearch.WordTrace]
  refine ⟨153118416753895845537922247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102078944502597230358614831 153118416753895845537922247)
  ·
    refine ⟨229677625130843768306883371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153118416753895845537922247 229677625130843768306883371)
    ·
      refine ⟨344516437696265652460325057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229677625130843768306883371 344516437696265652460325057)
      ·
        refine ⟨258387328272199239345243793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344516437696265652460325057 258387328272199239345243793)
        ·
          refine ⟨193790496204149429508932845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258387328272199239345243793 193790496204149429508932845)
          ·
            refine ⟨72671436076556036065849817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193790496204149429508932845 72671436076556036065849817)
            ·
              refine ⟨54503577057417027049387363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72671436076556036065849817 54503577057417027049387363)
              ·
                refine ⟨81755365586125540574081045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54503577057417027049387363 81755365586125540574081045)
                ·
                  refine ⟨3832282761849634714410049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81755365586125540574081045 3832282761849634714410049)
                  ·
                    refine ⟨2874212071387226035807537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3832282761849634714410049 2874212071387226035807537)
                    ·
                      refine ⟨2155659053540419526855653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2874212071387226035807537 2155659053540419526855653)
                      ·
                        rfl

theorem cell23_4198131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6, 2, 2].length) (baseStart_4198131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198131 prefixEnd_4198131 := by exact prefixLift 4198131
  have htrace : WordTrace (prefixWord ++ tailWord_4198131) baseStart_4198131 baseEnd_4198131 := by
    simpa [prefixWord, tailWord_4198131, baseEnd_4198131] using wordTrace_append hprefix tailTrace_4198131
  have hstable : (prefixWord ++ tailWord_4198131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198131).length < 2 ^ (prefixWord ++ tailWord_4198131).sum := by decide
  have hdescent : baseEnd_4198131 < baseStart_4198131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198147 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 7]
def baseStart_4198147 : Nat := 118140960795 + 4198147 * 2 ^ 59
def prefixEnd_4198147 : Nat := 4983230072969 + 3 ^ 40 * 4198147 * 2
def baseEnd_4198147 : Nat := 2155667269230891464255579

theorem tailTrace_4198147 : CollatzResearch.WordTrace tailWord_4198147 prefixEnd_4198147 2155667269230891464255579 := by
  unfold tailWord_4198147
  simp only [CollatzResearch.WordTrace]
  refine ⟨153119000321837880270504695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102079333547891920180336463 153119000321837880270504695)
  ·
    refine ⟨229678500482756820405757043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153119000321837880270504695 229678500482756820405757043)
    ·
      refine ⟨344517750724135230608635565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229678500482756820405757043 344517750724135230608635565)
      ·
        refine ⟨129194156521550711478238337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 344517750724135230608635565 129194156521550711478238337)
        ·
          refine ⟨96895617391163033608678753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129194156521550711478238337 96895617391163033608678753)
          ·
            refine ⟨72671713043372275206509065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96895617391163033608678753 72671713043372275206509065)
            ·
              refine ⟨54503784782529206404881799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72671713043372275206509065 54503784782529206404881799)
              ·
                refine ⟨81755677173793809607322699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54503784782529206404881799 81755677173793809607322699)
                ·
                  refine ⟨122633515760690714410984049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81755677173793809607322699 122633515760690714410984049)
                  ·
                    refine ⟨91975136820518035808238037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 122633515760690714410984049 91975136820518035808238037)
                    ·
                      refine ⟨2155667269230891464255579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91975136820518035808238037 2155667269230891464255579)
                      ·
                        rfl

theorem cell23_4198147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_4198147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198147 prefixEnd_4198147 := by exact prefixLift 4198147
  have htrace : WordTrace (prefixWord ++ tailWord_4198147) baseStart_4198147 baseEnd_4198147 := by
    simpa [prefixWord, tailWord_4198147, baseEnd_4198147] using wordTrace_append hprefix tailTrace_4198147
  have hstable : (prefixWord ++ tailWord_4198147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198147).length < 2 ^ (prefixWord ++ tailWord_4198147).sum := by decide
  have hdescent : baseEnd_4198147 < baseStart_4198147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198187 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 8]
def baseStart_4198187 : Nat := 118140960795 + 4198187 * 2 ^ 59
def prefixEnd_4198187 : Nat := 4983230072969 + 3 ^ 40 * 4198187 * 2
def baseEnd_4198187 : Nat := 2155687808457071307755395

theorem tailTrace_4198187 : CollatzResearch.WordTrace tailWord_4198187 prefixEnd_4198187 2155687808457071307755395 := by
  unfold tailWord_4198187
  simp only [CollatzResearch.WordTrace]
  refine ⟨153120459241692967101960815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102080306161128644734640543 153120459241692967101960815)
  ·
    refine ⟨229680688862539450652941223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153120459241692967101960815 229680688862539450652941223)
    ·
      refine ⟨344521033293809175979411835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229680688862539450652941223 344521033293809175979411835)
      ·
        refine ⟨516781549940713763969117753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344521033293809175979411835 516781549940713763969117753)
        ·
          refine ⟨387586162455535322976838315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 516781549940713763969117753 387586162455535322976838315)
          ·
            refine ⟨581379243683302984465257473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387586162455535322976838315 581379243683302984465257473)
            ·
              refine ⟨436034432762477238348943105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 581379243683302984465257473 436034432762477238348943105)
              ·
                refine ⟨327025824571857928761707329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 436034432762477238348943105 327025824571857928761707329)
                ·
                  refine ⟨245269368428893446571280497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 327025824571857928761707329 245269368428893446571280497)
                  ·
                    refine ⟨183952026321670084928460373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 245269368428893446571280497 183952026321670084928460373)
                    ·
                      refine ⟨2155687808457071307755395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 183952026321670084928460373 2155687808457071307755395)
                      ·
                        rfl

theorem cell23_4198187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 8].length) (baseStart_4198187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198187 prefixEnd_4198187 := by exact prefixLift 4198187
  have htrace : WordTrace (prefixWord ++ tailWord_4198187) baseStart_4198187 baseEnd_4198187 := by
    simpa [prefixWord, tailWord_4198187, baseEnd_4198187] using wordTrace_append hprefix tailTrace_4198187
  have hstable : (prefixWord ++ tailWord_4198187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198187).length < 2 ^ (prefixWord ++ tailWord_4198187).sum := by decide
  have hdescent : baseEnd_4198187 < baseStart_4198187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198198 : List Nat := [5, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_4198198 : Nat := 118140960795 + 4198198 * 2 ^ 59
def prefixEnd_4198198 : Nat := 4983230072969 + 3 ^ 40 * 4198198 * 2
def baseEnd_4198198 : Nat := 2155693456744270764717845

theorem tailTrace_4198198 : CollatzResearch.WordTrace tailWord_4198198 prefixEnd_4198198 2155693456744270764717845 := by
  unfold tailWord_4198198
  simp only [CollatzResearch.WordTrace]
  refine ⟨9570053777790819748788203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102080573629768743987074165 9570053777790819748788203)
  ·
    refine ⟨14355080666686229623182305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9570053777790819748788203 14355080666686229623182305)
    ·
      refine ⟨10766310500014672217386729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14355080666686229623182305 10766310500014672217386729)
      ·
        refine ⟨8074732875011004163040047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10766310500014672217386729 8074732875011004163040047)
        ·
          refine ⟨12112099312516506244560071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8074732875011004163040047 12112099312516506244560071)
          ·
            refine ⟨18168148968774759366840107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12112099312516506244560071 18168148968774759366840107)
            ·
              refine ⟨27252223453162139050260161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18168148968774759366840107 27252223453162139050260161)
              ·
                refine ⟨20439167589871604287695121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27252223453162139050260161 20439167589871604287695121)
                ·
                  refine ⟨15329375692403703215771341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20439167589871604287695121 15329375692403703215771341)
                  ·
                    refine ⟨5748515884651388705914253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15329375692403703215771341 5748515884651388705914253)
                    ·
                      refine ⟨2155693456744270764717845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5748515884651388705914253 2155693456744270764717845)
                      ·
                        rfl

theorem cell23_4198198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_4198198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198198 prefixEnd_4198198 := by exact prefixLift 4198198
  have htrace : WordTrace (prefixWord ++ tailWord_4198198) baseStart_4198198 baseEnd_4198198 := by
    simpa [prefixWord, tailWord_4198198, baseEnd_4198198] using wordTrace_append hprefix tailTrace_4198198
  have hstable : (prefixWord ++ tailWord_4198198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198198).length < 2 ^ (prefixWord ++ tailWord_4198198).sum := by decide
  have hdescent : baseEnd_4198198 < baseStart_4198198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198234 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4]
def baseStart_4198234 : Nat := 118140960795 + 4198234 * 2 ^ 59
def prefixEnd_4198234 : Nat := 4983230072969 + 3 ^ 40 * 4198234 * 2
def baseEnd_4198234 : Nat := 2155711942047832623867679

theorem tailTrace_4198234 : CollatzResearch.WordTrace tailWord_4198234 prefixEnd_4198234 2155711942047832623867679 := by
  unfold tailWord_4198234
  simp only [CollatzResearch.WordTrace]
  refine ⟨38280543368130673532230439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102081448981681796085947837 38280543368130673532230439)
  ·
    refine ⟨57420815052196010298345659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38280543368130673532230439 57420815052196010298345659)
    ·
      refine ⟨86131222578294015447518489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57420815052196010298345659 86131222578294015447518489)
      ·
        refine ⟨64598416933720511585638867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86131222578294015447518489 64598416933720511585638867)
        ·
          refine ⟨96897625400580767378458301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64598416933720511585638867 96897625400580767378458301)
          ·
            refine ⟨36336609525217787766921863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96897625400580767378458301 36336609525217787766921863)
            ·
              refine ⟨54504914287826681650382795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36336609525217787766921863 54504914287826681650382795)
              ·
                refine ⟨81757371431740022475574193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54504914287826681650382795 81757371431740022475574193)
                ·
                  refine ⟨61318028573805016856680645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81757371431740022475574193 61318028573805016856680645)
                  ·
                    refine ⟨11497130357588440660627621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61318028573805016856680645 11497130357588440660627621)
                    ·
                      refine ⟨2155711942047832623867679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11497130357588440660627621 2155711942047832623867679)
                      ·
                        rfl

theorem cell23_4198234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_4198234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198234 prefixEnd_4198234 := by exact prefixLift 4198234
  have htrace : WordTrace (prefixWord ++ tailWord_4198234) baseStart_4198234 baseEnd_4198234 := by
    simpa [prefixWord, tailWord_4198234, baseEnd_4198234] using wordTrace_append hprefix tailTrace_4198234
  have hstable : (prefixWord ++ tailWord_4198234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198234).length < 2 ^ (prefixWord ++ tailWord_4198234).sum := by decide
  have hdescent : baseEnd_4198234 < baseStart_4198234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198241 : List Nat := [1, 2, 3, 1, 1, 1, 4, 3, 2, 2, 3]
def baseStart_4198241 : Nat := 118140960795 + 4198241 * 2 ^ 59
def prefixEnd_4198241 : Nat := 4983230072969 + 3 ^ 40 * 4198241 * 2
def baseEnd_4198241 : Nat := 2155715536412414096480147

theorem tailTrace_4198241 : CollatzResearch.WordTrace tailWord_4198241 prefixEnd_4198241 2155715536412414096480147 := by
  unfold tailWord_4198241
  simp only [CollatzResearch.WordTrace]
  refine ⟨153122428783497334324426577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102081619188998222882951051 153122428783497334324426577)
  ·
    refine ⟨114841821587623000743319933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153122428783497334324426577 114841821587623000743319933)
    ·
      refine ⟨43065683095358625278744975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114841821587623000743319933 43065683095358625278744975)
      ·
        refine ⟨64598524643037937918117463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43065683095358625278744975 64598524643037937918117463)
        ·
          refine ⟨96897786964556906877176195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64598524643037937918117463 96897786964556906877176195)
          ·
            refine ⟨145346680446835360315764293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96897786964556906877176195 145346680446835360315764293)
            ·
              refine ⟨27252502583781630059205805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145346680446835360315764293 27252502583781630059205805)
              ·
                refine ⟨10219688468918111272202177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27252502583781630059205805 10219688468918111272202177)
                ·
                  refine ⟨7664766351688583454151633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10219688468918111272202177 7664766351688583454151633)
                  ·
                    refine ⟨5748574763766437590613725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7664766351688583454151633 5748574763766437590613725)
                    ·
                      refine ⟨2155715536412414096480147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5748574763766437590613725 2155715536412414096480147)
                      ·
                        rfl

theorem cell23_4198241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_4198241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198241 prefixEnd_4198241 := by exact prefixLift 4198241
  have htrace : WordTrace (prefixWord ++ tailWord_4198241) baseStart_4198241 baseEnd_4198241 := by
    simpa [prefixWord, tailWord_4198241, baseEnd_4198241] using wordTrace_append hprefix tailTrace_4198241
  have hstable : (prefixWord ++ tailWord_4198241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198241).length < 2 ^ (prefixWord ++ tailWord_4198241).sum := by decide
  have hdescent : baseEnd_4198241 < baseStart_4198241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198261 : List Nat := [1, 3, 4, 1, 1, 1, 2, 4, 6]
def baseStart_4198261 : Nat := 118140960795 + 4198261 * 2 ^ 59
def prefixEnd_4198261 : Nat := 4983230072969 + 3 ^ 40 * 4198261 * 2
def baseEnd_4198261 : Nat := 239525089558389335358895

theorem tailTrace_4198261 : CollatzResearch.WordTrace tailWord_4198261 prefixEnd_4198261 239525089558389335358895 := by
  unfold tailWord_4198261
  simp only [CollatzResearch.WordTrace]
  refine ⟨153123158243424877740154637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102082105495616585160103091 153123158243424877740154637)
  ·
    refine ⟨57421184341284329152557989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153123158243424877740154637 57421184341284329152557989)
    ·
      refine ⟨10766472063990811716104623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57421184341284329152557989 10766472063990811716104623)
      ·
        refine ⟨16149708095986217574156935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10766472063990811716104623 16149708095986217574156935)
        ·
          refine ⟨24224562143979326361235403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16149708095986217574156935 24224562143979326361235403)
          ·
            refine ⟨36336843215968989541853105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24224562143979326361235403 36336843215968989541853105)
            ·
              refine ⟨27252632411976742156389829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36336843215968989541853105 27252632411976742156389829)
              ·
                refine ⟨5109868577245639154323093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27252632411976742156389829 5109868577245639154323093)
                ·
                  refine ⟨239525089558389335358895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5109868577245639154323093 239525089558389335358895)
                  ·
                    rfl

theorem cell23_4198261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 6].length) (baseStart_4198261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198261 prefixEnd_4198261 := by exact prefixLift 4198261
  have htrace : WordTrace (prefixWord ++ tailWord_4198261) baseStart_4198261 baseEnd_4198261 := by
    simpa [prefixWord, tailWord_4198261, baseEnd_4198261] using wordTrace_append hprefix tailTrace_4198261
  have hstable : (prefixWord ++ tailWord_4198261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198261).length < 2 ^ (prefixWord ++ tailWord_4198261).sum := by decide
  have hdescent : baseEnd_4198261 < baseStart_4198261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198265 : List Nat := [1, 2, 1, 3, 2, 2, 5, 2, 1, 4]
def baseStart_4198265 : Nat := 118140960795 + 4198265 * 2 ^ 59
def prefixEnd_4198265 : Nat := 4983230072969 + 3 ^ 40 * 4198265 * 2
def baseEnd_4198265 : Nat := 718575953316040667526679

theorem tailTrace_4198265 : CollatzResearch.WordTrace tailWord_4198265 prefixEnd_4198265 718575953316040667526679 := by
  unfold tailWord_4198265
  simp only [CollatzResearch.WordTrace]
  refine ⟨153123304135410386423300249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102082202756940257615533499 153123304135410386423300249)
  ·
    refine ⟨114842478101557789817475187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153123304135410386423300249 114842478101557789817475187)
    ·
      refine ⟨172263717152336684726212781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114842478101557789817475187 172263717152336684726212781)
      ·
        refine ⟨64598893932126256772329793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172263717152336684726212781 64598893932126256772329793)
        ·
          refine ⟨48449170449094692579247345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64598893932126256772329793 48449170449094692579247345)
          ·
            refine ⟨36336877836821019434435509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48449170449094692579247345 36336877836821019434435509)
            ·
              refine ⟨3406582297201970571978329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36336877836821019434435509 3406582297201970571978329)
              ·
                refine ⟨2554936722901477928983747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3406582297201970571978329 2554936722901477928983747)
                ·
                  refine ⟨3832405084352216893475621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2554936722901477928983747 3832405084352216893475621)
                  ·
                    refine ⟨718575953316040667526679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3832405084352216893475621 718575953316040667526679)
                    ·
                      rfl

theorem cell23_4198265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2, 1, 4].length) (baseStart_4198265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198265 prefixEnd_4198265 := by exact prefixLift 4198265
  have htrace : WordTrace (prefixWord ++ tailWord_4198265) baseStart_4198265 baseEnd_4198265 := by
    simpa [prefixWord, tailWord_4198265, baseEnd_4198265] using wordTrace_append hprefix tailTrace_4198265
  have hstable : (prefixWord ++ tailWord_4198265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198265).length < 2 ^ (prefixWord ++ tailWord_4198265).sum := by decide
  have hdescent : baseEnd_4198265 < baseStart_4198265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198331 : List Nat := [1, 1, 1, 1, 1, 2, 2, 6, 3, 2, 3]
def baseStart_4198331 : Nat := 118140960795 + 4198331 * 2 ^ 59
def prefixEnd_4198331 : Nat := 4983230072969 + 3 ^ 40 * 4198331 * 2
def baseEnd_4198331 : Nat := 2155761749671318744354733

theorem tailTrace_4198331 : CollatzResearch.WordTrace tailWord_4198331 prefixEnd_4198331 2155761749671318744354733 := by
  unfold tailWord_4198331
  simp only [CollatzResearch.WordTrace]
  refine ⟨153125711353171279695202847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102083807568780853130135231 153125711353171279695202847)
  ·
    refine ⟨229688567029756919542804271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153125711353171279695202847 229688567029756919542804271)
    ·
      refine ⟨344532850544635379314206407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229688567029756919542804271 344532850544635379314206407)
      ·
        refine ⟨516799275816953068971309611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344532850544635379314206407 516799275816953068971309611)
        ·
          refine ⟨775198913725429603456964417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516799275816953068971309611 775198913725429603456964417)
          ·
            refine ⟨581399185294072202592723313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 775198913725429603456964417 581399185294072202592723313)
            ·
              refine ⟨436049388970554151944542485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 581399185294072202592723313 436049388970554151944542485)
              ·
                refine ⟨20439815107994725872400429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 436049388970554151944542485 20439815107994725872400429)
                ·
                  refine ⟨7664930665498022202150161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20439815107994725872400429 7664930665498022202150161)
                  ·
                    refine ⟨5748697999123516651612621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7664930665498022202150161 5748697999123516651612621)
                    ·
                      refine ⟨2155761749671318744354733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5748697999123516651612621 2155761749671318744354733)
                      ·
                        rfl

theorem cell23_4198331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2, 3].length) (baseStart_4198331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198331 prefixEnd_4198331 := by exact prefixLift 4198331
  have htrace : WordTrace (prefixWord ++ tailWord_4198331) baseStart_4198331 baseEnd_4198331 := by
    simpa [prefixWord, tailWord_4198331, baseEnd_4198331] using wordTrace_append hprefix tailTrace_4198331
  have hstable : (prefixWord ++ tailWord_4198331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198331).length < 2 ^ (prefixWord ++ tailWord_4198331).sum := by decide
  have hdescent : baseEnd_4198331 < baseStart_4198331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198348 : List Nat := [2, 2, 1, 4, 1, 2, 2, 1, 3, 2, 3]
def baseStart_4198348 : Nat := 118140960795 + 4198348 * 2 ^ 59
def prefixEnd_4198348 : Nat := 4983230072969 + 3 ^ 40 * 4198348 * 2
def baseEnd_4198348 : Nat := 2155770478842445177842155

theorem tailTrace_4198348 : CollatzResearch.WordTrace tailWord_4198348 prefixEnd_4198348 2155770478842445177842155 := by
  unfold tailWord_4198348
  simp only [CollatzResearch.WordTrace]
  refine ⟨76563165697054845799285849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102084220929406461065714465 76563165697054845799285849)
  ·
    refine ⟨57422374272791134349464387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76563165697054845799285849 57422374272791134349464387)
    ·
      refine ⟨86133561409186701524196581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57422374272791134349464387 86133561409186701524196581)
      ·
        refine ⟨16150042764222506535786859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86133561409186701524196581 16150042764222506535786859)
        ·
          refine ⟨24225064146333759803680289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16150042764222506535786859 24225064146333759803680289)
          ·
            refine ⟨18168798109750319852760217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24225064146333759803680289 18168798109750319852760217)
            ·
              refine ⟨13626598582312739889570163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18168798109750319852760217 13626598582312739889570163)
              ·
                refine ⟨20439897873469109834355245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13626598582312739889570163 20439897873469109834355245)
                ·
                  refine ⟨7664961702550916187883217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20439897873469109834355245 7664961702550916187883217)
                  ·
                    refine ⟨5748721276913187140912413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7664961702550916187883217 5748721276913187140912413)
                    ·
                      refine ⟨2155770478842445177842155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5748721276913187140912413 2155770478842445177842155)
                      ·
                        rfl

theorem cell23_4198348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_4198348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198348 prefixEnd_4198348 := by exact prefixLift 4198348
  have htrace : WordTrace (prefixWord ++ tailWord_4198348) baseStart_4198348 baseEnd_4198348 := by
    simpa [prefixWord, tailWord_4198348, baseEnd_4198348] using wordTrace_append hprefix tailTrace_4198348
  have hstable : (prefixWord ++ tailWord_4198348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198348).length < 2 ^ (prefixWord ++ tailWord_4198348).sum := by decide
  have hdescent : baseEnd_4198348 < baseStart_4198348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198351 : List Nat := [1, 1, 2, 1, 1, 5, 5, 7]
def baseStart_4198351 : Nat := 118140960795 + 4198351 * 2 ^ 59
def prefixEnd_4198351 : Nat := 4983230072969 + 3 ^ 40 * 4198351 * 2
def baseEnd_4198351 : Nat := 79843408121644765411283

theorem tailTrace_4198351 : CollatzResearch.WordTrace tailWord_4198351 prefixEnd_4198351 79843408121644765411283 := by
  unfold tailWord_4198351
  simp only [CollatzResearch.WordTrace]
  refine ⟨153126440813098823110930907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102084293875399215407287271 153126440813098823110930907)
  ·
    refine ⟨229689661219648234666396361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153126440813098823110930907 229689661219648234666396361)
    ·
      refine ⟨172267245914736175999797271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229689661219648234666396361 172267245914736175999797271)
      ·
        refine ⟨258400868872104263999695907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172267245914736175999797271 258400868872104263999695907)
        ·
          refine ⟨387601303308156395999543861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258400868872104263999695907 387601303308156395999543861)
          ·
            refine ⟨36337622185139662124957237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 387601303308156395999543861 36337622185139662124957237)
            ·
              refine ⟨3406652079856843324214741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36337622185139662124957237 3406652079856843324214741)
              ·
                refine ⟨79843408121644765411283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3406652079856843324214741 79843408121644765411283)
                ·
                  rfl

theorem cell23_4198351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 7].length) (baseStart_4198351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198351 prefixEnd_4198351 := by exact prefixLift 4198351
  have htrace : WordTrace (prefixWord ++ tailWord_4198351) baseStart_4198351 baseEnd_4198351 := by
    simpa [prefixWord, tailWord_4198351, baseEnd_4198351] using wordTrace_append hprefix tailTrace_4198351
  have hstable : (prefixWord ++ tailWord_4198351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198351).length < 2 ^ (prefixWord ++ tailWord_4198351).sum := by decide
  have hdescent : baseEnd_4198351 < baseStart_4198351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198362 : List Nat := [3, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4]
def baseStart_4198362 : Nat := 118140960795 + 4198362 * 2 ^ 59
def prefixEnd_4198362 : Nat := 4983230072969 + 3 ^ 40 * 4198362 * 2
def baseEnd_4198362 : Nat := 2155777667571608123067091

theorem tailTrace_4198362 : CollatzResearch.WordTrace tailWord_4198362 prefixEnd_4198362 2155777667571608123067091 := by
  unfold tailWord_4198362
  simp only [CollatzResearch.WordTrace]
  refine ⟨38281710504014742997395335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102084561344039314659720893 38281710504014742997395335)
  ·
    refine ⟨57422565756022114496093003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38281710504014742997395335 57422565756022114496093003)
    ·
      refine ⟨86133848634033171744139505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57422565756022114496093003 86133848634033171744139505)
      ·
        refine ⟨64600386475524878808104629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86133848634033171744139505 64600386475524878808104629)
        ·
          refine ⟨6056286232080457388259809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64600386475524878808104629 6056286232080457388259809)
          ·
            refine ⟨4542214674060343041194857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6056286232080457388259809 4542214674060343041194857)
            ·
              refine ⟨3406661005545257280896143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4542214674060343041194857 3406661005545257280896143)
              ·
                refine ⟨5109991508317885921344215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3406661005545257280896143 5109991508317885921344215)
                ·
                  refine ⟨7664987262476828882016323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5109991508317885921344215 7664987262476828882016323)
                  ·
                    refine ⟨11497480893715243323024485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7664987262476828882016323 11497480893715243323024485)
                    ·
                      refine ⟨2155777667571608123067091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11497480893715243323024485 2155777667571608123067091)
                      ·
                        rfl

theorem cell23_4198362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4].length) (baseStart_4198362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198362 prefixEnd_4198362 := by exact prefixLift 4198362
  have htrace : WordTrace (prefixWord ++ tailWord_4198362) baseStart_4198362 baseEnd_4198362 := by
    simpa [prefixWord, tailWord_4198362, baseEnd_4198362] using wordTrace_append hprefix tailTrace_4198362
  have hstable : (prefixWord ++ tailWord_4198362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198362).length < 2 ^ (prefixWord ++ tailWord_4198362).sum := by decide
  have hdescent : baseEnd_4198362 < baseStart_4198362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198405 : List Nat := [1, 3, 1, 1, 2, 4, 1, 4, 1, 3, 2]
def baseStart_4198405 : Nat := 118140960795 + 4198405 * 2 ^ 59
def prefixEnd_4198405 : Nat := 4983230072969 + 3 ^ 40 * 4198405 * 2
def baseEnd_4198405 : Nat := 2155799747239751454829393

theorem tailTrace_4198405 : CollatzResearch.WordTrace tailWord_4198405 prefixEnd_4198405 2155799747239751454829393 := by
  unfold tailWord_4198405
  simp only [CollatzResearch.WordTrace]
  refine ⟨153128410354903190333396669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102085606903268793555597779 153128410354903190333396669)
  ·
    refine ⟨57423153883088696375023751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153128410354903190333396669 57423153883088696375023751)
    ·
      refine ⟨86134730824633044562535627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57423153883088696375023751 86134730824633044562535627)
      ·
        refine ⟨129202096236949566843803441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86134730824633044562535627 129202096236949566843803441)
        ·
          refine ⟨96901572177712175132852581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129202096236949566843803441 96901572177712175132852581)
          ·
            refine ⟨18169044783321032837409859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96901572177712175132852581 18169044783321032837409859)
            ·
              refine ⟨27253567174981549256114789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18169044783321032837409859 27253567174981549256114789)
              ·
                refine ⟨5110043845309040485521523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27253567174981549256114789 5110043845309040485521523)
                ·
                  refine ⟨7665065767963560728282285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5110043845309040485521523 7665065767963560728282285)
                  ·
                    refine ⟨2874399662986335273105857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7665065767963560728282285 2874399662986335273105857)
                    ·
                      refine ⟨2155799747239751454829393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2874399662986335273105857 2155799747239751454829393)
                      ·
                        rfl

theorem cell23_4198405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 3, 2].length) (baseStart_4198405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198405 prefixEnd_4198405 := by exact prefixLift 4198405
  have htrace : WordTrace (prefixWord ++ tailWord_4198405) baseStart_4198405 baseEnd_4198405 := by
    simpa [prefixWord, tailWord_4198405, baseEnd_4198405] using wordTrace_append hprefix tailTrace_4198405
  have hstable : (prefixWord ++ tailWord_4198405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198405).length < 2 ^ (prefixWord ++ tailWord_4198405).sum := by decide
  have hdescent : baseEnd_4198405 < baseStart_4198405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198435 : List Nat := [1, 1, 1, 4, 3, 1, 1, 3, 4, 2, 2]
def baseStart_4198435 : Nat := 118140960795 + 4198435 * 2 ^ 59
def prefixEnd_4198435 : Nat := 4983230072969 + 3 ^ 40 * 4198435 * 2
def baseEnd_4198435 : Nat := 2155815151659386337454255

theorem tailTrace_4198435 : CollatzResearch.WordTrace tailWord_4198435 prefixEnd_4198435 2155815151659386337454255 := by
  unfold tailWord_4198435
  simp only [CollatzResearch.WordTrace]
  refine ⟨153129504544794505456988759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102086336363196336971325839 153129504544794505456988759)
  ·
    refine ⟨229694256817191758185483139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153129504544794505456988759 229694256817191758185483139)
    ·
      refine ⟨344541385225787637278224709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229694256817191758185483139 344541385225787637278224709)
      ·
        refine ⟨64601509729835181989667133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 344541385225787637278224709 64601509729835181989667133)
        ·
          refine ⟨24225566148688193246125175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64601509729835181989667133 24225566148688193246125175)
          ·
            refine ⟨36338349223032289869187763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24225566148688193246125175 36338349223032289869187763)
            ·
              refine ⟨54507523834548434803781645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36338349223032289869187763 54507523834548434803781645)
              ·
                refine ⟨20440321437955663051418117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54507523834548434803781645 20440321437955663051418117)
                ·
                  refine ⟨3832560269616686822140897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20440321437955663051418117 3832560269616686822140897)
                  ·
                    refine ⟨2874420202212515116605673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3832560269616686822140897 2874420202212515116605673)
                    ·
                      refine ⟨2155815151659386337454255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2874420202212515116605673 2155815151659386337454255)
                      ·
                        rfl

theorem cell23_4198435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4, 2, 2].length) (baseStart_4198435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198435 prefixEnd_4198435 := by exact prefixLift 4198435
  have htrace : WordTrace (prefixWord ++ tailWord_4198435) baseStart_4198435 baseEnd_4198435 := by
    simpa [prefixWord, tailWord_4198435, baseEnd_4198435] using wordTrace_append hprefix tailTrace_4198435
  have hstable : (prefixWord ++ tailWord_4198435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198435).length < 2 ^ (prefixWord ++ tailWord_4198435).sum := by decide
  have hdescent : baseEnd_4198435 < baseStart_4198435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198486 : List Nat := [5, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_4198486 : Nat := 118140960795 + 4198486 * 2 ^ 59
def prefixEnd_4198486 : Nat := 4983230072969 + 3 ^ 40 * 4198486 * 2
def baseEnd_4198486 : Nat := 2155841339172765637916521

theorem tailTrace_4198486 : CollatzResearch.WordTrace tailWord_4198486 prefixEnd_4198486 2155841339172765637916521 := by
  unfold tailWord_4198486
  simp only [CollatzResearch.WordTrace]
  refine ⟨9570710291725608822943457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102087576445073160778063541 9570710291725608822943457)
  ·
    refine ⟨7178032718794206617207593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9570710291725608822943457 7178032718794206617207593)
    ·
      refine ⟨5383524539095654962905695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7178032718794206617207593 5383524539095654962905695)
      ·
        refine ⟨8075286808643482444358543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5383524539095654962905695 8075286808643482444358543)
        ·
          refine ⟨12112930212965223666537815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8075286808643482444358543 12112930212965223666537815)
          ·
            refine ⟨18169395319447835499806723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12112930212965223666537815 18169395319447835499806723)
            ·
              refine ⟨27254092979171753249710085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18169395319447835499806723 27254092979171753249710085)
              ·
                refine ⟨5110142433594703734320641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27254092979171753249710085 5110142433594703734320641)
                ·
                  refine ⟨3832606825196027800740481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5110142433594703734320641 3832606825196027800740481)
                  ·
                    refine ⟨2874455118897020850555361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3832606825196027800740481 2874455118897020850555361)
                    ·
                      refine ⟨2155841339172765637916521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2874455118897020850555361 2155841339172765637916521)
                      ·
                        rfl

theorem cell23_4198486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_4198486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198486 prefixEnd_4198486 := by exact prefixLift 4198486
  have htrace : WordTrace (prefixWord ++ tailWord_4198486) baseStart_4198486 baseEnd_4198486 := by
    simpa [prefixWord, tailWord_4198486, baseEnd_4198486] using wordTrace_append hprefix tailTrace_4198486
  have hstable : (prefixWord ++ tailWord_4198486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198486).length < 2 ^ (prefixWord ++ tailWord_4198486).sum := by decide
  have hdescent : baseEnd_4198486 < baseStart_4198486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198488 : List Nat := [2, 1, 2, 2, 1, 4, 2, 2, 2, 5]
def baseStart_4198488 : Nat := 118140960795 + 4198488 * 2 ^ 59
def prefixEnd_4198488 : Nat := 4983230072969 + 3 ^ 40 * 4198488 * 2
def baseEnd_4198488 : Nat := 718614122044691543363837

theorem tailTrace_4198488 : CollatzResearch.WordTrace tailWord_4198488 prefixEnd_4198488 718614122044691543363837 := by
  unfold tailWord_4198488
  simp only [CollatzResearch.WordTrace]
  refine ⟨76565718806801247754334059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102087625075734997005778745 76565718806801247754334059)
  ·
    refine ⟨114848578210201871631501089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76565718806801247754334059 114848578210201871631501089)
    ·
      refine ⟨86136433657651403723625817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114848578210201871631501089 86136433657651403723625817)
      ·
        refine ⟨64602325243238552792719363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86136433657651403723625817 64602325243238552792719363)
        ·
          refine ⟨96903487864857829189079045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64602325243238552792719363 96903487864857829189079045)
          ·
            refine ⟨18169403974660842972952321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96903487864857829189079045 18169403974660842972952321)
            ·
              refine ⟨13627052980995632229714241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18169403974660842972952321 13627052980995632229714241)
              ·
                refine ⟨10220289735746724172285681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13627052980995632229714241 10220289735746724172285681)
                ·
                  refine ⟨7665217301810043129214261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10220289735746724172285681 7665217301810043129214261)
                  ·
                    refine ⟨718614122044691543363837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7665217301810043129214261 718614122044691543363837)
                    ·
                      rfl

theorem cell23_4198488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 2, 5].length) (baseStart_4198488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198488 prefixEnd_4198488 := by exact prefixLift 4198488
  have htrace : WordTrace (prefixWord ++ tailWord_4198488) baseStart_4198488 baseEnd_4198488 := by
    simpa [prefixWord, tailWord_4198488, baseEnd_4198488] using wordTrace_append hprefix tailTrace_4198488
  have hstable : (prefixWord ++ tailWord_4198488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198488).length < 2 ^ (prefixWord ++ tailWord_4198488).sum := by decide
  have hdescent : baseEnd_4198488 < baseStart_4198488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198492 : List Nat := [2, 2, 4, 1, 1, 2, 4, 2, 5]
def baseStart_4198492 : Nat := 118140960795 + 4198492 * 2 ^ 59
def prefixEnd_4198492 : Nat := 4983230072969 + 3 ^ 40 * 4198492 * 2
def baseEnd_4198492 : Nat := 239538268895188068271277

theorem tailTrace_4198492 : CollatzResearch.WordTrace tailWord_4198492 prefixEnd_4198492 239538268895188068271277 := by
  unfold tailWord_4198492
  simp only [CollatzResearch.WordTrace]
  refine ⟨76565791752794002095906865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102087722337058669461209153 76565791752794002095906865)
  ·
    refine ⟨57424343814595501571930149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76565791752794002095906865 57424343814595501571930149)
    ·
      refine ⟨10767064465236656544736903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57424343814595501571930149 10767064465236656544736903)
      ·
        refine ⟨16150596697854984817105355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10767064465236656544736903 16150596697854984817105355)
        ·
          refine ⟨24225895046782477225658033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16150596697854984817105355 24225895046782477225658033)
          ·
            refine ⟨18169421285086857919243525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24225895046782477225658033 18169421285086857919243525)
            ·
              refine ⟨3406766490953785859858161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18169421285086857919243525 3406766490953785859858161)
              ·
                refine ⟨2555074868215339394893621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3406766490953785859858161 2555074868215339394893621)
                ·
                  refine ⟨239538268895188068271277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2555074868215339394893621 239538268895188068271277)
                  ·
                    rfl

theorem cell23_4198492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2, 5].length) (baseStart_4198492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198492 prefixEnd_4198492 := by exact prefixLift 4198492
  have htrace : WordTrace (prefixWord ++ tailWord_4198492) baseStart_4198492 baseEnd_4198492 := by
    simpa [prefixWord, tailWord_4198492, baseEnd_4198492] using wordTrace_append hprefix tailTrace_4198492
  have hstable : (prefixWord ++ tailWord_4198492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198492).length < 2 ^ (prefixWord ++ tailWord_4198492).sum := by decide
  have hdescent : baseEnd_4198492 < baseStart_4198492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198525 : List Nat := [1, 4, 1, 1, 3, 2, 3, 1, 2, 1, 4]
def baseStart_4198525 : Nat := 118140960795 + 4198525 * 2 ^ 59
def prefixEnd_4198525 : Nat := 4983230072969 + 3 ^ 40 * 4198525 * 2
def baseEnd_4198525 : Nat := 2155861364918290985328841

theorem tailTrace_4198525 : CollatzResearch.WordTrace tailWord_4198525 prefixEnd_4198525 2155861364918290985328841 := by
  unfold tailWord_4198525
  simp only [CollatzResearch.WordTrace]
  refine ⟨153132787114468450827765029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102088524742978967218510019 153132787114468450827765029)
  ·
    refine ⟨28712397583962834530205943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153132787114468450827765029 28712397583962834530205943)
    ·
      refine ⟨43068596375944251795308915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28712397583962834530205943 43068596375944251795308915)
      ·
        refine ⟨64602894563916377692963373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43068596375944251795308915 64602894563916377692963373)
        ·
          refine ⟨24226085461468641634861265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64602894563916377692963373 24226085461468641634861265)
          ·
            refine ⟨18169564096101481226145949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24226085461468641634861265 18169564096101481226145949)
            ·
              refine ⟨6813586536038055459804731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18169564096101481226145949 6813586536038055459804731)
              ·
                refine ⟨10220379804057083189707097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6813586536038055459804731 10220379804057083189707097)
                ·
                  refine ⟨7665284853042812392280323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10220379804057083189707097 7665284853042812392280323)
                  ·
                    refine ⟨11497927279564218588420485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7665284853042812392280323 11497927279564218588420485)
                    ·
                      refine ⟨2155861364918290985328841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11497927279564218588420485 2155861364918290985328841)
                      ·
                        rfl

theorem cell23_4198525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_4198525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198525 prefixEnd_4198525 := by exact prefixLift 4198525
  have htrace : WordTrace (prefixWord ++ tailWord_4198525) baseStart_4198525 baseEnd_4198525 := by
    simpa [prefixWord, tailWord_4198525, baseEnd_4198525] using wordTrace_append hprefix tailTrace_4198525
  have hstable : (prefixWord ++ tailWord_4198525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198525).length < 2 ^ (prefixWord ++ tailWord_4198525).sum := by decide
  have hdescent : baseEnd_4198525 < baseStart_4198525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198538 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 2, 1, 6]
def baseStart_4198538 : Nat := 118140960795 + 4198538 * 2 ^ 59
def prefixEnd_4198538 : Nat := 4983230072969 + 3 ^ 40 * 4198538 * 2
def baseEnd_4198538 : Nat := 2155868040166799434466281

theorem tailTrace_4198538 : CollatzResearch.WordTrace tailWord_4198538 prefixEnd_4198538 2155868040166799434466281 := by
  unfold tailWord_4198538
  simp only [CollatzResearch.WordTrace]
  refine ⟨38283315315855338511997067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102088840842280902698658845 38283315315855338511997067)
  ·
    refine ⟨57424972973783007767995601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38283315315855338511997067 57424972973783007767995601)
    ·
      refine ⟨43068729730337255825996701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57424972973783007767995601 43068729730337255825996701)
      ·
        refine ⟨16150773648876470934748763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43068729730337255825996701 16150773648876470934748763)
        ·
          refine ⟨24226160473314706402123145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16150773648876470934748763 24226160473314706402123145)
          ·
            refine ⟨18169620354986029801592359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24226160473314706402123145 18169620354986029801592359)
            ·
              refine ⟨27254430532479044702388539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18169620354986029801592359 27254430532479044702388539)
              ·
                refine ⟨40881645798718567053582809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27254430532479044702388539 40881645798718567053582809)
                ·
                  refine ⟨30661234349038925290187107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40881645798718567053582809 30661234349038925290187107)
                  ·
                    refine ⟨45991851523558387935280661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30661234349038925290187107 45991851523558387935280661)
                    ·
                      refine ⟨2155868040166799434466281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45991851523558387935280661 2155868040166799434466281)
                      ·
                        rfl

theorem cell23_4198538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_4198538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198538 prefixEnd_4198538 := by exact prefixLift 4198538
  have htrace : WordTrace (prefixWord ++ tailWord_4198538) baseStart_4198538 baseEnd_4198538 := by
    simpa [prefixWord, tailWord_4198538, baseEnd_4198538] using wordTrace_append hprefix tailTrace_4198538
  have hstable : (prefixWord ++ tailWord_4198538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198538).length < 2 ^ (prefixWord ++ tailWord_4198538).sum := by decide
  have hdescent : baseEnd_4198538 < baseStart_4198538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198552 : List Nat := [2, 1, 2, 4, 3, 1, 2, 1, 3, 4]
def baseStart_4198552 : Nat := 118140960795 + 4198552 * 2 ^ 59
def prefixEnd_4198552 : Nat := 4983230072969 + 3 ^ 40 * 4198552 * 2
def baseEnd_4198552 : Nat := 718625076298654126563739

theorem tailTrace_4198552 : CollatzResearch.WordTrace tailWord_4198552 prefixEnd_4198552 718625076298654126563739 := by
  unfold tailWord_4198552
  simp only [CollatzResearch.WordTrace]
  refine ⟨76566885942685317219498955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102089181256913756292665273 76566885942685317219498955)
  ·
    refine ⟨114850328914027975829248433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76566885942685317219498955 114850328914027975829248433)
    ·
      refine ⟨86137746685520981871936325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114850328914027975829248433 86137746685520981871936325)
      ·
        refine ⟨16150827503535184100988061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86137746685520981871936325 16150827503535184100988061)
        ·
          refine ⟨6056560313825694037870523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16150827503535184100988061 6056560313825694037870523)
          ·
            refine ⟨9084840470738541056805785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6056560313825694037870523 9084840470738541056805785)
            ·
              refine ⟨6813630353053905792604339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9084840470738541056805785 6813630353053905792604339)
              ·
                refine ⟨10220445529580858688906509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6813630353053905792604339 10220445529580858688906509)
                ·
                  refine ⟨3832667073592822008339941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10220445529580858688906509 3832667073592822008339941)
                  ·
                    refine ⟨718625076298654126563739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3832667073592822008339941 718625076298654126563739)
                    ·
                      rfl

theorem cell23_4198552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 3, 4].length) (baseStart_4198552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198552 prefixEnd_4198552 := by exact prefixLift 4198552
  have htrace : WordTrace (prefixWord ++ tailWord_4198552) baseStart_4198552 baseEnd_4198552 := by
    simpa [prefixWord, tailWord_4198552, baseEnd_4198552] using wordTrace_append hprefix tailTrace_4198552
  have hstable : (prefixWord ++ tailWord_4198552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198552).length < 2 ^ (prefixWord ++ tailWord_4198552).sum := by decide
  have hdescent : baseEnd_4198552 < baseStart_4198552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198565 : List Nat := [1, 3, 1, 2, 1, 3, 5, 1, 6]
def baseStart_4198565 : Nat := 118140960795 + 4198565 * 2 ^ 59
def prefixEnd_4198565 : Nat := 4983230072969 + 3 ^ 40 * 4198565 * 2
def baseEnd_4198565 : Nat := 239542433793830092092073

theorem tailTrace_4198565 : CollatzResearch.WordTrace tailWord_4198565 prefixEnd_4198565 239542433793830092092073 := by
  unfold tailWord_4198565
  simp only [CollatzResearch.WordTrace]
  refine ⟨153134246034323537659221149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102089497356215691772814099 153134246034323537659221149)
  ·
    refine ⟨57425342262871326622207931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153134246034323537659221149 57425342262871326622207931)
    ·
      refine ⟨86138013394306989933311897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57425342262871326622207931 86138013394306989933311897)
      ·
        refine ⟨64603510045730242449983923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86138013394306989933311897 64603510045730242449983923)
        ·
          refine ⟨96905265068595363674975885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64603510045730242449983923 96905265068595363674975885)
          ·
            refine ⟨36339474400723261378115957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96905265068595363674975885 36339474400723261378115957)
            ·
              refine ⟨3406825725067805754198371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36339474400723261378115957 3406825725067805754198371)
              ·
                refine ⟨5110238587601708631297557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3406825725067805754198371 5110238587601708631297557)
                ·
                  refine ⟨239542433793830092092073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5110238587601708631297557 239542433793830092092073)
                  ·
                    rfl

theorem cell23_4198565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 6].length) (baseStart_4198565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198565 prefixEnd_4198565 := by exact prefixLift 4198565
  have htrace : WordTrace (prefixWord ++ tailWord_4198565) baseStart_4198565 baseEnd_4198565 := by
    simpa [prefixWord, tailWord_4198565, baseEnd_4198565] using wordTrace_append hprefix tailTrace_4198565
  have hstable : (prefixWord ++ tailWord_4198565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198565).length < 2 ^ (prefixWord ++ tailWord_4198565).sum := by decide
  have hdescent : baseEnd_4198565 < baseStart_4198565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198585 : List Nat := [1, 2, 1, 4, 1, 2, 1, 3, 1, 5, 2]
def baseStart_4198585 : Nat := 118140960795 + 4198585 * 2 ^ 59
def prefixEnd_4198585 : Nat := 4983230072969 + 3 ^ 40 * 4198585 * 2
def baseEnd_4198585 : Nat := 2155892173757560750578565

theorem tailTrace_4198585 : CollatzResearch.WordTrace tailWord_4198585 prefixEnd_4198585 2155892173757560750578565 := by
  unfold tailWord_4198585
  simp only [CollatzResearch.WordTrace]
  refine ⟨153134975494251081074949209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102089983662834054049966139 153134975494251081074949209)
  ·
    refine ⟨114851231620688310806211907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153134975494251081074949209 114851231620688310806211907)
    ·
      refine ⟨172276847431032466209317861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114851231620688310806211907 172276847431032466209317861)
      ·
        refine ⟨32301908893318587414247099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172276847431032466209317861 32301908893318587414247099)
        ·
          refine ⟨48452863339977881121370649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32301908893318587414247099 48452863339977881121370649)
          ·
            refine ⟨36339647504983410841027987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48452863339977881121370649 36339647504983410841027987)
            ·
              refine ⟨54509471257475116261541981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36339647504983410841027987 54509471257475116261541981)
              ·
                refine ⟨20441051721553168598078243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54509471257475116261541981 20441051721553168598078243)
                ·
                  refine ⟨30661577582329752897117365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20441051721553168598078243 30661577582329752897117365)
                  ·
                    refine ⟨2874522898343414334104753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30661577582329752897117365 2874522898343414334104753)
                    ·
                      refine ⟨2155892173757560750578565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2874522898343414334104753 2155892173757560750578565)
                      ·
                        rfl

theorem cell23_4198585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_4198585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198585 prefixEnd_4198585 := by exact prefixLift 4198585
  have htrace : WordTrace (prefixWord ++ tailWord_4198585) baseStart_4198585 baseEnd_4198585 := by
    simpa [prefixWord, tailWord_4198585, baseEnd_4198585] using wordTrace_append hprefix tailTrace_4198585
  have hstable : (prefixWord ++ tailWord_4198585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198585).length < 2 ^ (prefixWord ++ tailWord_4198585).sum := by decide
  have hdescent : baseEnd_4198585 < baseStart_4198585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198602 : List Nat := [3, 1, 2, 1, 3, 1, 3, 2, 2, 3, 2]
def baseStart_4198602 : Nat := 118140960795 + 4198602 * 2 ^ 59
def prefixEnd_4198602 : Nat := 4983230072969 + 3 ^ 40 * 4198602 * 2
def baseEnd_4198602 : Nat := 2155900902928687184065987

theorem tailTrace_4198602 : CollatzResearch.WordTrace tailWord_4198602 prefixEnd_4198602 2155900902928687184065987 := by
  unfold tailWord_4198602
  simp only [CollatzResearch.WordTrace]
  refine ⟨38283898883797373244579515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102090397023459661985545373 38283898883797373244579515)
  ·
    refine ⟨57425848325696059866869273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38283898883797373244579515 57425848325696059866869273)
    ·
      refine ⟨43069386244272044900151955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57425848325696059866869273 43069386244272044900151955)
      ·
        refine ⟨64604079366408067350227933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43069386244272044900151955 64604079366408067350227933)
        ·
          refine ⟨24226529762403025256335475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64604079366408067350227933 24226529762403025256335475)
          ·
            refine ⟨36339794643604537884503213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24226529762403025256335475 36339794643604537884503213)
            ·
              refine ⟨13627422991351701706688705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36339794643604537884503213 13627422991351701706688705)
              ·
                refine ⟨10220567243513776280016529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13627422991351701706688705 10220567243513776280016529)
                ·
                  refine ⟨7665425432635332210012397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10220567243513776280016529 7665425432635332210012397)
                  ·
                    refine ⟨2874534537238249578754649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7665425432635332210012397 2874534537238249578754649)
                    ·
                      refine ⟨2155900902928687184065987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2874534537238249578754649 2155900902928687184065987)
                      ·
                        rfl

theorem cell23_4198602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 2, 3, 2].length) (baseStart_4198602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198602 prefixEnd_4198602 := by exact prefixLift 4198602
  have htrace : WordTrace (prefixWord ++ tailWord_4198602) baseStart_4198602 baseEnd_4198602 := by
    simpa [prefixWord, tailWord_4198602, baseEnd_4198602] using wordTrace_append hprefix tailTrace_4198602
  have hstable : (prefixWord ++ tailWord_4198602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198602).length < 2 ^ (prefixWord ++ tailWord_4198602).sum := by decide
  have hdescent : baseEnd_4198602 < baseStart_4198602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198632 : List Nat := [2, 1, 4, 1, 2, 2, 3, 2, 1, 1, 4]
def baseStart_4198632 : Nat := 118140960795 + 4198632 * 2 ^ 59
def prefixEnd_4198632 : Nat := 4983230072969 + 3 ^ 40 * 4198632 * 2
def baseEnd_4198632 : Nat := 2155916307348322066690849

theorem tailTrace_4198632 : CollatzResearch.WordTrace tailWord_4198632 prefixEnd_4198632 2155916307348322066690849 := by
  unfold tailWord_4198632
  simp only [CollatzResearch.WordTrace]
  refine ⟨76568344862540404050955075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102091126483387205401273433 76568344862540404050955075)
  ·
    refine ⟨114852517293810606076432613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76568344862540404050955075 114852517293810606076432613)
    ·
      refine ⟨21534846992589488639331115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114852517293810606076432613 21534846992589488639331115)
      ·
        refine ⟨32302270488884232958996673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21534846992589488639331115 32302270488884232958996673)
        ·
          refine ⟨24226702866663174719247505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32302270488884232958996673 24226702866663174719247505)
          ·
            refine ⟨18170027149997381039435629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24226702866663174719247505 18170027149997381039435629)
            ·
              refine ⟨6813760181249017889788361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18170027149997381039435629 6813760181249017889788361)
              ·
                refine ⟨5110320135936763417341271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6813760181249017889788361 5110320135936763417341271)
                ·
                  refine ⟨7665480203905145126011907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5110320135936763417341271 7665480203905145126011907)
                  ·
                    refine ⟨11498220305857717689017861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7665480203905145126011907 11498220305857717689017861)
                    ·
                      refine ⟨2155916307348322066690849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11498220305857717689017861 2155916307348322066690849)
                      ·
                        rfl

theorem cell23_4198632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_4198632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198632 prefixEnd_4198632 := by exact prefixLift 4198632
  have htrace : WordTrace (prefixWord ++ tailWord_4198632) baseStart_4198632 baseEnd_4198632 := by
    simpa [prefixWord, tailWord_4198632, baseEnd_4198632] using wordTrace_append hprefix tailTrace_4198632
  have hstable : (prefixWord ++ tailWord_4198632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198632).length < 2 ^ (prefixWord ++ tailWord_4198632).sum := by decide
  have hdescent : baseEnd_4198632 < baseStart_4198632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198635 : List Nat := [1, 1, 1, 1, 2, 5, 3, 1, 3, 2, 3]
def baseStart_4198635 : Nat := 118140960795 + 4198635 * 2 ^ 59
def prefixEnd_4198635 : Nat := 4983230072969 + 3 ^ 40 * 4198635 * 2
def baseEnd_4198635 : Nat := 2155917847790285554953335

theorem tailTrace_4198635 : CollatzResearch.WordTrace tailWord_4198635 prefixEnd_4198635 2155917847790285554953335 := by
  unfold tailWord_4198635
  simp only [CollatzResearch.WordTrace]
  refine ⟨153136799144069939614269359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102091199429379959742846239 153136799144069939614269359)
  ·
    refine ⟨229705198716104909421404039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153136799144069939614269359 229705198716104909421404039)
    ·
      refine ⟨344557798074157364132106059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229705198716104909421404039 344557798074157364132106059)
      ·
        refine ⟨516836697111236046198159089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344557798074157364132106059 516836697111236046198159089)
        ·
          refine ⟨387627522833427034648619317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 516836697111236046198159089 387627522833427034648619317)
          ·
            refine ⟨36340080265633784498308061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 387627522833427034648619317 36340080265633784498308061)
            ·
              refine ⟨13627530099612669186865523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36340080265633784498308061 13627530099612669186865523)
              ·
                refine ⟨20441295149419003780298285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13627530099612669186865523 20441295149419003780298285)
                ·
                  refine ⟨7665485681032126417611857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20441295149419003780298285 7665485681032126417611857)
                  ·
                    refine ⟨5749114260774094813208893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7665485681032126417611857 5749114260774094813208893)
                    ·
                      refine ⟨2155917847790285554953335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5749114260774094813208893 2155917847790285554953335)
                      ·
                        rfl

theorem cell23_4198635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2, 3].length) (baseStart_4198635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198635 prefixEnd_4198635 := by exact prefixLift 4198635
  have htrace : WordTrace (prefixWord ++ tailWord_4198635) baseStart_4198635 baseEnd_4198635 := by
    simpa [prefixWord, tailWord_4198635, baseEnd_4198635] using wordTrace_append hprefix tailTrace_4198635
  have hstable : (prefixWord ++ tailWord_4198635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198635).length < 2 ^ (prefixWord ++ tailWord_4198635).sum := by decide
  have hdescent : baseEnd_4198635 < baseStart_4198635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198652 : List Nat := [2, 2, 2, 1, 4, 3, 1, 1, 1, 1, 5]
def baseStart_4198652 : Nat := 118140960795 + 4198652 * 2 ^ 59
def prefixEnd_4198652 : Nat := 4983230072969 + 3 ^ 40 * 4198652 * 2
def baseEnd_4198652 : Nat := 2155926576961411988440757

theorem tailTrace_4198652 : CollatzResearch.WordTrace tailWord_4198652 prefixEnd_4198652 2155926576961411988440757 := by
  unfold tailWord_4198652
  simp only [CollatzResearch.WordTrace]
  refine ⟨76568709592504175758819105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102091612790005567678425473 76568709592504175758819105)
  ·
    refine ⟨57426532194378131819114329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76568709592504175758819105 57426532194378131819114329)
    ·
      refine ⟨43069899145783598864335747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57426532194378131819114329 43069899145783598864335747)
      ·
        refine ⟨64604848718675398296503621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43069899145783598864335747 64604848718675398296503621)
        ·
          refine ⟨12113409134751637180594429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64604848718675398296503621 12113409134751637180594429)
          ·
            refine ⟨4542528425531863942722911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12113409134751637180594429 4542528425531863942722911)
            ·
              refine ⟨6813792638297795914084367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4542528425531863942722911 6813792638297795914084367)
              ·
                refine ⟨10220688957446693871126551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6813792638297795914084367 10220688957446693871126551)
                ·
                  refine ⟨15331033436170040806689827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10220688957446693871126551 15331033436170040806689827)
                  ·
                    refine ⟨22996550154255061210034741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15331033436170040806689827 22996550154255061210034741)
                    ·
                      refine ⟨2155926576961411988440757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22996550154255061210034741 2155926576961411988440757)
                      ·
                        rfl

theorem cell23_4198652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_4198652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198652 prefixEnd_4198652 := by exact prefixLift 4198652
  have htrace : WordTrace (prefixWord ++ tailWord_4198652) baseStart_4198652 baseEnd_4198652 := by
    simpa [prefixWord, tailWord_4198652, baseEnd_4198652] using wordTrace_append hprefix tailTrace_4198652
  have hstable : (prefixWord ++ tailWord_4198652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198652).length < 2 ^ (prefixWord ++ tailWord_4198652).sum := by decide
  have hdescent : baseEnd_4198652 < baseStart_4198652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198660 : List Nat := [2, 3, 2, 2, 4, 1, 2, 2, 1, 1, 3]
def baseStart_4198660 : Nat := 118140960795 + 4198660 * 2 ^ 59
def prefixEnd_4198660 : Nat := 4983230072969 + 3 ^ 40 * 4198660 * 2
def baseEnd_4198660 : Nat := 2155930684806647957140721

theorem tailTrace_4198660 : CollatzResearch.WordTrace tailWord_4198660 prefixEnd_4198660 2155930684806647957140721 := by
  unfold tailWord_4198660
  simp only [CollatzResearch.WordTrace]
  refine ⟨76568855484489684441964717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102091807312652912589286289 76568855484489684441964717)
  ·
    refine ⟨28713320806683631665736769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76568855484489684441964717 28713320806683631665736769)
    ·
      refine ⟨21534990605012723749302577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28713320806683631665736769 21534990605012723749302577)
      ·
        refine ⟨16151242953759542811976933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21534990605012723749302577 16151242953759542811976933)
        ·
          refine ⟨3028358053829914277245675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16151242953759542811976933 3028358053829914277245675)
          ·
            refine ⟨4542537080744871415868513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3028358053829914277245675 4542537080744871415868513)
            ·
              refine ⟨3406902810558653561901385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4542537080744871415868513 3406902810558653561901385)
              ·
                refine ⟨2555177107918990171426039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3406902810558653561901385 2555177107918990171426039)
                ·
                  refine ⟨3832765661878485257139059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2555177107918990171426039 3832765661878485257139059)
                  ·
                    refine ⟨5749148492817727885708589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3832765661878485257139059 5749148492817727885708589)
                    ·
                      refine ⟨2155930684806647957140721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5749148492817727885708589 2155930684806647957140721)
                      ·
                        rfl

theorem cell23_4198660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_4198660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198660 prefixEnd_4198660 := by exact prefixLift 4198660
  have htrace : WordTrace (prefixWord ++ tailWord_4198660) baseStart_4198660 baseEnd_4198660 := by
    simpa [prefixWord, tailWord_4198660, baseEnd_4198660] using wordTrace_append hprefix tailTrace_4198660
  have hstable : (prefixWord ++ tailWord_4198660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198660).length < 2 ^ (prefixWord ++ tailWord_4198660).sum := by decide
  have hdescent : baseEnd_4198660 < baseStart_4198660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198668 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 1, 9]
def baseStart_4198668 : Nat := 118140960795 + 4198668 * 2 ^ 59
def prefixEnd_4198668 : Nat := 4983230072969 + 3 ^ 40 * 4198668 * 2
def baseEnd_4198668 : Nat := 718644930883961308613561

theorem tailTrace_4198668 : CollatzResearch.WordTrace tailWord_4198668 prefixEnd_4198668 718644930883961308613561 := by
  unfold tailWord_4198668
  simp only [CollatzResearch.WordTrace]
  refine ⟨76569001376475193125110329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102092001835300257500147105 76569001376475193125110329)
  ·
    refine ⟨57426751032356394843832747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76569001376475193125110329 57426751032356394843832747)
    ·
      refine ⟨86140126548534592265749121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57426751032356394843832747 86140126548534592265749121)
      ·
        refine ⟨64605094911400944199311841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86140126548534592265749121 64605094911400944199311841)
        ·
          refine ⟨48453821183550708149483881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64605094911400944199311841 48453821183550708149483881)
          ·
            refine ⟨36340365887663031112112911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48453821183550708149483881 36340365887663031112112911)
            ·
              refine ⟨54510548831494546668169367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36340365887663031112112911 54510548831494546668169367)
              ·
                refine ⟨81765823247241820002254051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54510548831494546668169367 81765823247241820002254051)
                ·
                  refine ⟨122648734870862730003381077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81765823247241820002254051 122648734870862730003381077)
                  ·
                    refine ⟨718644930883961308613561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 122648734870862730003381077 718644930883961308613561)
                    ·
                      rfl

theorem cell23_4198668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_4198668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198668 prefixEnd_4198668 := by exact prefixLift 4198668
  have htrace : WordTrace (prefixWord ++ tailWord_4198668) baseStart_4198668 baseEnd_4198668 := by
    simpa [prefixWord, tailWord_4198668, baseEnd_4198668] using wordTrace_append hprefix tailTrace_4198668
  have hstable : (prefixWord ++ tailWord_4198668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198668).length < 2 ^ (prefixWord ++ tailWord_4198668).sum := by decide
  have hdescent : baseEnd_4198668 < baseStart_4198668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198709 : List Nat := [1, 3, 3, 1, 2, 1, 3, 3, 1, 3, 2]
def baseStart_4198709 : Nat := 118140960795 + 4198709 * 2 ^ 59
def prefixEnd_4198709 : Nat := 4983230072969 + 3 ^ 40 * 4198709 * 2
def baseEnd_4198709 : Nat := 2155955845358718265427995

theorem tailTrace_4198709 : CollatzResearch.WordTrace tailWord_4198709 prefixEnd_4198709 2155955845358718265427995 := by
  unfold tailWord_4198709
  simp only [CollatzResearch.WordTrace]
  refine ⟨153139498145801850252463181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102092998763867900168308787 153139498145801850252463181)
  ·
    refine ⟨57427311804675693844673693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153139498145801850252463181 57427311804675693844673693)
    ·
      refine ⟨21535241926753385191752635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57427311804675693844673693 21535241926753385191752635)
      ·
        refine ⟨32302862890130077787628953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21535241926753385191752635 32302862890130077787628953)
        ·
          refine ⟨24227147167597558340721715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32302862890130077787628953 24227147167597558340721715)
          ·
            refine ⟨36340720751396337511082573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24227147167597558340721715 36340720751396337511082573)
            ·
              refine ⟨13627770281773626566655965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36340720751396337511082573 13627770281773626566655965)
              ·
                refine ⟨5110413855665109962495987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13627770281773626566655965 5110413855665109962495987)
                ·
                  refine ⟨7665620783497664943743981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5110413855665109962495987 7665620783497664943743981)
                  ·
                    refine ⟨2874607793811624353903993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7665620783497664943743981 2874607793811624353903993)
                    ·
                      refine ⟨2155955845358718265427995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2874607793811624353903993 2155955845358718265427995)
                      ·
                        rfl

theorem cell23_4198709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_4198709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198709 prefixEnd_4198709 := by exact prefixLift 4198709
  have htrace : WordTrace (prefixWord ++ tailWord_4198709) baseStart_4198709 baseEnd_4198709 := by
    simpa [prefixWord, tailWord_4198709, baseEnd_4198709] using wordTrace_append hprefix tailTrace_4198709
  have hstable : (prefixWord ++ tailWord_4198709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198709).length < 2 ^ (prefixWord ++ tailWord_4198709).sum := by decide
  have hdescent : baseEnd_4198709 < baseStart_4198709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198779 : List Nat := [1, 1, 1, 1, 1, 8, 3, 2, 5]
def baseStart_4198779 : Nat := 118140960795 + 4198779 * 2 ^ 59
def prefixEnd_4198779 : Nat := 4983230072969 + 3 ^ 40 * 4198779 * 2
def baseEnd_4198779 : Nat := 239554643222725887950297

theorem tailTrace_4198779 : CollatzResearch.WordTrace tailWord_4198779 prefixEnd_4198779 239554643222725887950297 := by
  unfold tailWord_4198779
  simp only [CollatzResearch.WordTrace]
  refine ⟨153142051255548252207511391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102094700837032168138340927 153142051255548252207511391)
  ·
    refine ⟨229713076883322378311267087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153142051255548252207511391 229713076883322378311267087)
    ·
      refine ⟨344569615324983567466900631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229713076883322378311267087 344569615324983567466900631)
      ·
        refine ⟨516854422987475351200350947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344569615324983567466900631 516854422987475351200350947)
        ·
          refine ⟨775281634481213026800526421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516854422987475351200350947 775281634481213026800526421)
          ·
            refine ⟨9085331654076715157818669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 775281634481213026800526421 9085331654076715157818669)
            ·
              refine ⟨3406999370278768184182001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9085331654076715157818669 3406999370278768184182001)
              ·
                refine ⟨2555249527709076138136501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3406999370278768184182001 2555249527709076138136501)
                ·
                  refine ⟨239554643222725887950297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2555249527709076138136501 239554643222725887950297)
                  ·
                    rfl

theorem cell23_4198779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2, 5].length) (baseStart_4198779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198779 prefixEnd_4198779 := by exact prefixLift 4198779
  have htrace : WordTrace (prefixWord ++ tailWord_4198779) baseStart_4198779 baseEnd_4198779 := by
    simpa [prefixWord, tailWord_4198779, baseEnd_4198779] using wordTrace_append hprefix tailTrace_4198779
  have hstable : (prefixWord ++ tailWord_4198779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198779).length < 2 ^ (prefixWord ++ tailWord_4198779).sum := by decide
  have hdescent : baseEnd_4198779 < baseStart_4198779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198866 : List Nat := [3, 2, 2, 4, 1, 1, 1, 1, 1, 4, 3]
def baseStart_4198866 : Nat := 118140960795 + 4198866 * 2 ^ 59
def prefixEnd_4198866 : Nat := 4983230072969 + 3 ^ 40 * 4198866 * 2
def baseEnd_4198866 : Nat := 2156036461821474151164773

theorem tailTrace_4198866 : CollatzResearch.WordTrace tailWord_4198866 prefixEnd_4198866 2156036461821474151164773 := by
  unfold tailWord_4198866
  simp only [CollatzResearch.WordTrace]
  refine ⟨38286306101558266516482113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102096816270822044043952301 38286306101558266516482113)
  ·
    refine ⟨28714729576168699887361585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38286306101558266516482113 28714729576168699887361585)
    ·
      refine ⟨21536047182126524915521189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28714729576168699887361585 21536047182126524915521189)
      ·
        refine ⟨4038008846648723421660223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21536047182126524915521189 4038008846648723421660223)
        ·
          refine ⟨6057013269973085132490335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4038008846648723421660223 6057013269973085132490335)
          ·
            refine ⟨9085519904959627698735503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6057013269973085132490335 9085519904959627698735503)
            ·
              refine ⟨13628279857439441548103255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9085519904959627698735503 13628279857439441548103255)
              ·
                refine ⟨20442419786159162322154883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13628279857439441548103255 20442419786159162322154883)
                ·
                  refine ⟨30663629679238743483232325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20442419786159162322154883 30663629679238743483232325)
                  ·
                    refine ⟨5749430564857264403106061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30663629679238743483232325 5749430564857264403106061)
                    ·
                      refine ⟨2156036461821474151164773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5749430564857264403106061 2156036461821474151164773)
                      ·
                        rfl

theorem cell23_4198866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_4198866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198866 prefixEnd_4198866 := by exact prefixLift 4198866
  have htrace : WordTrace (prefixWord ++ tailWord_4198866) baseStart_4198866 baseEnd_4198866 := by
    simpa [prefixWord, tailWord_4198866, baseEnd_4198866] using wordTrace_append hprefix tailTrace_4198866
  have hstable : (prefixWord ++ tailWord_4198866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198866).length < 2 ^ (prefixWord ++ tailWord_4198866).sum := by decide
  have hdescent : baseEnd_4198866 < baseStart_4198866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198896 : List Nat := [2, 1, 1, 1, 3, 3, 1, 6, 1, 1, 3]
def baseStart_4198896 : Nat := 118140960795 + 4198896 * 2 ^ 59
def prefixEnd_4198896 : Nat := 4983230072969 + 3 ^ 40 * 4198896 * 2
def baseEnd_4198896 : Nat := 2156051866241109033789635

theorem tailTrace_4198896 : CollatzResearch.WordTrace tailWord_4198896 prefixEnd_4198896 2156051866241109033789635 := by
  unfold tailWord_4198896
  simp only [CollatzResearch.WordTrace]
  refine ⟨76573159298062190594760271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102097545730749587459680361 76573159298062190594760271)
  ·
    refine ⟨114859738947093285892140407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76573159298062190594760271 114859738947093285892140407)
    ·
      refine ⟨172289608420639928838210611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114859738947093285892140407 172289608420639928838210611)
      ·
        refine ⟨258434412630959893257315917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172289608420639928838210611 258434412630959893257315917)
        ·
          refine ⟨96912904736609959971493469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 258434412630959893257315917 96912904736609959971493469)
          ·
            refine ⟨36342339276228734989310051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96912904736609959971493469 36342339276228734989310051)
            ·
              refine ⟨54513508914343102483965077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36342339276228734989310051 54513508914343102483965077)
              ·
                refine ⟨2555320730359832928935863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54513508914343102483965077 2555320730359832928935863)
                ·
                  refine ⟨3832981095539749393403795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2555320730359832928935863 3832981095539749393403795)
                  ·
                    refine ⟨5749471643309624090105693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3832981095539749393403795 5749471643309624090105693)
                    ·
                      refine ⟨2156051866241109033789635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5749471643309624090105693 2156051866241109033789635)
                      ·
                        rfl

theorem cell23_4198896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6, 1, 1, 3].length) (baseStart_4198896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198896 prefixEnd_4198896 := by exact prefixLift 4198896
  have htrace : WordTrace (prefixWord ++ tailWord_4198896) baseStart_4198896 baseEnd_4198896 := by
    simpa [prefixWord, tailWord_4198896, baseEnd_4198896] using wordTrace_append hprefix tailTrace_4198896
  have hstable : (prefixWord ++ tailWord_4198896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198896).length < 2 ^ (prefixWord ++ tailWord_4198896).sum := by decide
  have hdescent : baseEnd_4198896 < baseStart_4198896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198916 : List Nat := [2, 3, 2, 3, 1, 2, 2, 2, 1, 5]
def baseStart_4198916 : Nat := 118140960795 + 4198916 * 2 ^ 59
def prefixEnd_4198916 : Nat := 4983230072969 + 3 ^ 40 * 4198916 * 2
def baseEnd_4198916 : Nat := 718687378618066318513181

theorem tailTrace_4198916 : CollatzResearch.WordTrace tailWord_4198916 prefixEnd_4198916 718687378618066318513181 := by
  unfold tailWord_4198916
  simp only [CollatzResearch.WordTrace]
  refine ⟨76573524028025962302624301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102098032037367949736832401 76573524028025962302624301)
  ·
    refine ⟨28715071510509735863484113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76573524028025962302624301 28715071510509735863484113)
    ·
      refine ⟨21536303632882301897613085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28715071510509735863484113 21536303632882301897613085)
      ·
        refine ⟨8076113862330863211604907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21536303632882301897613085 8076113862330863211604907)
        ·
          refine ⟨12114170793496294817407361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8076113862330863211604907 12114170793496294817407361)
          ·
            refine ⟨9085628095122221113055521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12114170793496294817407361 9085628095122221113055521)
            ·
              refine ⟨6814221071341665834791641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9085628095122221113055521 6814221071341665834791641)
              ·
                refine ⟨5110665803506249376093731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6814221071341665834791641 5110665803506249376093731)
                ·
                  refine ⟨7665998705259374064140597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5110665803506249376093731 7665998705259374064140597)
                  ·
                    refine ⟨718687378618066318513181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7665998705259374064140597 718687378618066318513181)
                    ·
                      rfl

theorem cell23_4198916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_4198916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198916 prefixEnd_4198916 := by exact prefixLift 4198916
  have htrace : WordTrace (prefixWord ++ tailWord_4198916) baseStart_4198916 baseEnd_4198916 := by
    simpa [prefixWord, tailWord_4198916, baseEnd_4198916] using wordTrace_append hprefix tailTrace_4198916
  have hstable : (prefixWord ++ tailWord_4198916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198916).length < 2 ^ (prefixWord ++ tailWord_4198916).sum := by decide
  have hdescent : baseEnd_4198916 < baseStart_4198916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198922 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 3, 1, 5]
def baseStart_4198922 : Nat := 118140960795 + 4198922 * 2 ^ 59
def prefixEnd_4198922 : Nat := 4983230072969 + 3 ^ 40 * 4198922 * 2
def baseEnd_4198922 : Nat := 2156065216738125932064515

theorem tailTrace_4198922 : CollatzResearch.WordTrace tailWord_4198922 prefixEnd_4198922 2156065216738125932064515 := by
  unfold tailWord_4198922
  simp only [CollatzResearch.WordTrace]
  refine ⟨38286816723507546907491755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102098177929353458419978013 38286816723507546907491755)
  ·
    refine ⟨57430225085261320361237633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38286816723507546907491755 57430225085261320361237633)
    ·
      refine ⟨43072668813945990270928225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57430225085261320361237633 43072668813945990270928225)
      ·
        refine ⟨32304501610459492703196169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43072668813945990270928225 32304501610459492703196169)
        ·
          refine ⟨24228376207844619527397127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32304501610459492703196169 24228376207844619527397127)
          ·
            refine ⟨36342564311766929291095691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24228376207844619527397127 36342564311766929291095691)
            ·
              refine ⟨54513846467650393936643537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36342564311766929291095691 54513846467650393936643537)
              ·
                refine ⟨40885384850737795452482653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54513846467650393936643537 40885384850737795452482653)
                ·
                  refine ⟨15332019319026673294680995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40885384850737795452482653 15332019319026673294680995)
                  ·
                    refine ⟨22998028978540009942021493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15332019319026673294680995 22998028978540009942021493)
                    ·
                      refine ⟨2156065216738125932064515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22998028978540009942021493 2156065216738125932064515)
                      ·
                        rfl

theorem cell23_4198922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_4198922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198922 prefixEnd_4198922 := by exact prefixLift 4198922
  have htrace : WordTrace (prefixWord ++ tailWord_4198922) baseStart_4198922 baseEnd_4198922 := by
    simpa [prefixWord, tailWord_4198922, baseEnd_4198922] using wordTrace_append hprefix tailTrace_4198922
  have hstable : (prefixWord ++ tailWord_4198922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198922).length < 2 ^ (prefixWord ++ tailWord_4198922).sum := by decide
  have hdescent : baseEnd_4198922 < baseStart_4198922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198969 : List Nat := [1, 2, 1, 5, 1, 1, 2, 3, 1, 3, 3]
def baseStart_4198969 : Nat := 118140960795 + 4198969 * 2 ^ 59
def prefixEnd_4198969 : Nat := 4983230072969 + 3 ^ 40 * 4198969 * 2
def baseEnd_4198969 : Nat := 2156089350328887248176799

theorem tailTrace_4198969 : CollatzResearch.WordTrace tailWord_4198969 prefixEnd_4198969 2156089350328887248176799 := by
  unfold tailWord_4198969
  simp only [CollatzResearch.WordTrace]
  refine ⟨153148981124859914656927961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102099320749906609771285307 153148981124859914656927961)
  ·
    refine ⟨114861735843644935992695971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153148981124859914656927961 114861735843644935992695971)
    ·
      refine ⟨172292603765467403989043957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114861735843644935992695971 172292603765467403989043957)
      ·
        refine ⟨16152431603012569123972871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 172292603765467403989043957 16152431603012569123972871)
        ·
          refine ⟨24228647404518853685959307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16152431603012569123972871 24228647404518853685959307)
          ·
            refine ⟨36342971106778280528938961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24228647404518853685959307 36342971106778280528938961)
            ·
              refine ⟨27257228330083710396704221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36342971106778280528938961 27257228330083710396704221)
              ·
                refine ⟨10221460623781391398764083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27257228330083710396704221 10221460623781391398764083)
                ·
                  refine ⟨15332190935672087098146125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10221460623781391398764083 15332190935672087098146125)
                  ·
                    refine ⟨5749571600877032661804797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15332190935672087098146125 5749571600877032661804797)
                    ·
                      refine ⟨2156089350328887248176799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5749571600877032661804797 2156089350328887248176799)
                      ·
                        rfl

theorem cell23_4198969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_4198969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198969 prefixEnd_4198969 := by exact prefixLift 4198969
  have htrace : WordTrace (prefixWord ++ tailWord_4198969) baseStart_4198969 baseEnd_4198969 := by
    simpa [prefixWord, tailWord_4198969, baseEnd_4198969] using wordTrace_append hprefix tailTrace_4198969
  have hstable : (prefixWord ++ tailWord_4198969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198969).length < 2 ^ (prefixWord ++ tailWord_4198969).sum := by decide
  have hdescent : baseEnd_4198969 < baseStart_4198969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4198973 : List Nat := [1, 4, 1, 3, 2, 3, 1, 2, 1, 2, 3]
def baseStart_4198973 : Nat := 118140960795 + 4198973 * 2 ^ 59
def prefixEnd_4198973 : Nat := 4983230072969 + 3 ^ 40 * 4198973 * 2
def baseEnd_4198973 : Nat := 2156091404251505232526781

theorem tailTrace_4198973 : CollatzResearch.WordTrace tailWord_4198973 prefixEnd_4198973 2156091404251505232526781 := by
  unfold tailWord_4198973
  simp only [CollatzResearch.WordTrace]
  refine ⟨153149127016845423340073573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102099418011230282226715715 153149127016845423340073573)
  ·
    refine ⟨28715461315658516876263795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153149127016845423340073573 28715461315658516876263795)
    ·
      refine ⟨43073191973487775314395693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28715461315658516876263795 43073191973487775314395693)
      ·
        refine ⟨16152446990057915742898385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43073191973487775314395693 16152446990057915742898385)
        ·
          refine ⟨12114335242543436807173789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16152446990057915742898385 12114335242543436807173789)
          ·
            refine ⟨4542875715953788802690171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12114335242543436807173789 4542875715953788802690171)
            ·
              refine ⟨6814313573930683204035257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4542875715953788802690171 6814313573930683204035257)
              ·
                refine ⟨5110735180448012403026443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6814313573930683204035257 5110735180448012403026443)
                ·
                  refine ⟨7666102770672018604539665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5110735180448012403026443 7666102770672018604539665)
                  ·
                    refine ⟨5749577078004013953404749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7666102770672018604539665 5749577078004013953404749)
                    ·
                      refine ⟨2156091404251505232526781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5749577078004013953404749 2156091404251505232526781)
                      ·
                        rfl

theorem cell23_4198973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_4198973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4198973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4198973 prefixEnd_4198973 := by exact prefixLift 4198973
  have htrace : WordTrace (prefixWord ++ tailWord_4198973) baseStart_4198973 baseEnd_4198973 := by
    simpa [prefixWord, tailWord_4198973, baseEnd_4198973] using wordTrace_append hprefix tailTrace_4198973
  have hstable : (prefixWord ++ tailWord_4198973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4198973).length < 2 ^ (prefixWord ++ tailWord_4198973).sum := by decide
  have hdescent : baseEnd_4198973 < baseStart_4198973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4198973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199004 : List Nat := [2, 2, 4, 1, 3, 2, 2, 2, 1, 2, 2]
def baseStart_4199004 : Nat := 118140960795 + 4199004 * 2 ^ 59
def prefixEnd_4199004 : Nat := 4983230072969 + 3 ^ 40 * 4199004 * 2
def baseEnd_4199004 : Nat := 2156107322151794611239139

theorem tailTrace_4199004 : CollatzResearch.WordTrace tailWord_4199004 prefixEnd_4199004 2156107322151794611239139 := by
  unfold tailWord_4199004
  simp only [CollatzResearch.WordTrace]
  refine ⟨76575128839866557817226033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102100171786488743756301377 76575128839866557817226033)
  ·
    refine ⟨57431346629899918362919525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76575128839866557817226033 57431346629899918362919525)
    ·
      refine ⟨10768377493106234693047411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57431346629899918362919525 10768377493106234693047411)
      ·
        refine ⟨16152566239659352039571117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10768377493106234693047411 16152566239659352039571117)
        ·
          refine ⟨6057212339872257014839169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16152566239659352039571117 6057212339872257014839169)
          ·
            refine ⟨4542909254904192761129377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6057212339872257014839169 4542909254904192761129377)
            ·
              refine ⟨3407181941178144570847033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4542909254904192761129377 3407181941178144570847033)
              ·
                refine ⟨2555386455883608428135275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3407181941178144570847033 2555386455883608428135275)
                ·
                  refine ⟨3833079683825412642202913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2555386455883608428135275 3833079683825412642202913)
                  ·
                    refine ⟨2874809762869059481652185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3833079683825412642202913 2874809762869059481652185)
                    ·
                      refine ⟨2156107322151794611239139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2874809762869059481652185 2156107322151794611239139)
                      ·
                        rfl

theorem cell23_4199004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_4199004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199004 prefixEnd_4199004 := by exact prefixLift 4199004
  have htrace : WordTrace (prefixWord ++ tailWord_4199004) baseStart_4199004 baseEnd_4199004 := by
    simpa [prefixWord, tailWord_4199004, baseEnd_4199004] using wordTrace_append hprefix tailTrace_4199004
  have hstable : (prefixWord ++ tailWord_4199004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199004).length < 2 ^ (prefixWord ++ tailWord_4199004).sum := by decide
  have hdescent : baseEnd_4199004 < baseStart_4199004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199032 : List Nat := [2, 1, 2, 1, 1, 1, 2, 6, 7]
def baseStart_4199032 : Nat := 118140960795 + 4199032 * 2 ^ 59
def prefixEnd_4199032 : Nat := 4983230072969 + 3 ^ 40 * 4199032 * 2
def baseEnd_4199032 : Nat := 239569077734457833521001

theorem tailTrace_4199032 : CollatzResearch.WordTrace tailWord_4199032 prefixEnd_4199032 239569077734457833521001 := by
  unfold tailWord_4199032
  simp only [CollatzResearch.WordTrace]
  refine ⟨76575639461815838208235675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102100852615754450944314233 76575639461815838208235675)
  ·
    refine ⟨114863459192723757312353513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76575639461815838208235675 114863459192723757312353513)
    ·
      refine ⟨86147594394542817984265135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114863459192723757312353513 86147594394542817984265135)
      ·
        refine ⟨129221391591814226976397703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86147594394542817984265135 129221391591814226976397703)
        ·
          refine ⟨193832087387721340464596555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129221391591814226976397703 193832087387721340464596555)
          ·
            refine ⟨290748131081582010696894833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193832087387721340464596555 290748131081582010696894833)
            ·
              refine ⟨218061098311186508022671125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290748131081582010696894833 218061098311186508022671125)
              ·
                refine ⟨10221613983336867563562709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 218061098311186508022671125 10221613983336867563562709)
                ·
                  refine ⟨239569077734457833521001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10221613983336867563562709 239569077734457833521001)
                  ·
                    rfl

theorem cell23_4199032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 7].length) (baseStart_4199032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199032 prefixEnd_4199032 := by exact prefixLift 4199032
  have htrace : WordTrace (prefixWord ++ tailWord_4199032) baseStart_4199032 baseEnd_4199032 := by
    simpa [prefixWord, tailWord_4199032, baseEnd_4199032] using wordTrace_append hprefix tailTrace_4199032
  have hstable : (prefixWord ++ tailWord_4199032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199032).length < 2 ^ (prefixWord ++ tailWord_4199032).sum := by decide
  have hdescent : baseEnd_4199032 < baseStart_4199032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199060 : List Nat := [2, 4, 2, 2, 1, 2, 1, 1, 4, 2, 2]
def baseStart_4199060 : Nat := 118140960795 + 4199060 * 2 ^ 59
def prefixEnd_4199060 : Nat := 4983230072969 + 3 ^ 40 * 4199060 * 2
def baseEnd_4199060 : Nat := 2156136077068446392138881

theorem tailTrace_4199060 : CollatzResearch.WordTrace tailWord_4199060 prefixEnd_4199060 2156136077068446392138881 := by
  unfold tailWord_4199060
  simp only [CollatzResearch.WordTrace]
  refine ⟨76576150083765118599245317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102101533445020158132327089 76576150083765118599245317)
  ·
    refine ⟨14358028140705959737358497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76576150083765118599245317 14358028140705959737358497)
    ·
      refine ⟨10768521105529469803018873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14358028140705959737358497 10768521105529469803018873)
      ·
        refine ⟨8076390829147102352264155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10768521105529469803018873 8076390829147102352264155)
        ·
          refine ⟨12114586243720653528396233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8076390829147102352264155 12114586243720653528396233)
          ·
            refine ⟨9085939682790490146297175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12114586243720653528396233 9085939682790490146297175)
            ·
              refine ⟨13628909524185735219445763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9085939682790490146297175 13628909524185735219445763)
              ·
                refine ⟨20443364286278602829168645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13628909524185735219445763 20443364286278602829168645)
                ·
                  refine ⟨3833130803677238030469121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20443364286278602829168645 3833130803677238030469121)
                  ·
                    refine ⟨2874848102757928522851841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3833130803677238030469121 2874848102757928522851841)
                    ·
                      refine ⟨2156136077068446392138881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2874848102757928522851841 2156136077068446392138881)
                      ·
                        rfl

theorem cell23_4199060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_4199060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199060 prefixEnd_4199060 := by exact prefixLift 4199060
  have htrace : WordTrace (prefixWord ++ tailWord_4199060) baseStart_4199060 baseEnd_4199060 := by
    simpa [prefixWord, tailWord_4199060, baseEnd_4199060] using wordTrace_append hprefix tailTrace_4199060
  have hstable : (prefixWord ++ tailWord_4199060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199060).length < 2 ^ (prefixWord ++ tailWord_4199060).sum := by decide
  have hdescent : baseEnd_4199060 < baseStart_4199060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199116 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 4, 1, 4]
def baseStart_4199116 : Nat := 118140960795 + 4199116 * 2 ^ 59
def prefixEnd_4199116 : Nat := 4983230072969 + 3 ^ 40 * 4199116 * 2
def baseEnd_4199116 : Nat := 2156164831985098173038623

theorem tailTrace_4199116 : CollatzResearch.WordTrace tailWord_4199116 prefixEnd_4199116 2156164831985098173038623 := by
  unfold tailWord_4199116
  simp only [CollatzResearch.WordTrace]
  refine ⟨76577171327663679381264601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102102895103551572508352801 76577171327663679381264601)
  ·
    refine ⟨57432878495747759535948451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76577171327663679381264601 57432878495747759535948451)
    ·
      refine ⟨86149317743621639303922677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57432878495747759535948451 86149317743621639303922677)
      ·
        refine ⟨8076498538464528684742751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86149317743621639303922677 8076498538464528684742751)
        ·
          refine ⟨12114747807696793027114127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8076498538464528684742751 12114747807696793027114127)
          ·
            refine ⟨18172121711545189540671191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12114747807696793027114127 18172121711545189540671191)
            ·
              refine ⟨27258182567317784311006787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18172121711545189540671191 27258182567317784311006787)
              ·
                refine ⟨40887273850976676466510181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27258182567317784311006787 40887273850976676466510181)
                ·
                  refine ⟨7666363847058126837470659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40887273850976676466510181 7666363847058126837470659)
                  ·
                    refine ⟨11499545770587190256205989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7666363847058126837470659 11499545770587190256205989)
                    ·
                      refine ⟨2156164831985098173038623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11499545770587190256205989 2156164831985098173038623)
                      ·
                        rfl

theorem cell23_4199116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_4199116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199116 prefixEnd_4199116 := by exact prefixLift 4199116
  have htrace : WordTrace (prefixWord ++ tailWord_4199116) baseStart_4199116 baseEnd_4199116 := by
    simpa [prefixWord, tailWord_4199116, baseEnd_4199116] using wordTrace_append hprefix tailTrace_4199116
  have hstable : (prefixWord ++ tailWord_4199116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199116).length < 2 ^ (prefixWord ++ tailWord_4199116).sum := by decide
  have hdescent : baseEnd_4199116 < baseStart_4199116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199117 : List Nat := [1, 6, 2, 1, 2, 1, 3, 2, 5]
def baseStart_4199117 : Nat := 118140960795 + 4199117 * 2 ^ 59
def prefixEnd_4199117 : Nat := 4983230072969 + 3 ^ 40 * 4199117 * 2
def baseEnd_4199117 : Nat := 239573927273972518791791

theorem tailTrace_4199117 : CollatzResearch.WordTrace tailWord_4199117 prefixEnd_4199117 239573927273972518791791 := by
  unfold tailWord_4199117
  simp only [CollatzResearch.WordTrace]
  refine ⟨153154379128323735933315605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102102919418882490622210403 153154379128323735933315605)
  ·
    refine ⟨7179111521640175121874169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 153154379128323735933315605 7179111521640175121874169)
    ·
      refine ⟨5384333641230131341405627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7179111521640175121874169 5384333641230131341405627)
      ·
        refine ⟨8076500461845197012108441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5384333641230131341405627 8076500461845197012108441)
        ·
          refine ⟨6057375346383897759081331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8076500461845197012108441 6057375346383897759081331)
          ·
            refine ⟨9086063019575846638621997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6057375346383897759081331 9086063019575846638621997)
            ·
              refine ⟨3407273632340942489483249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9086063019575846638621997 3407273632340942489483249)
              ·
                refine ⟨2555455224255706867112437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3407273632340942489483249 2555455224255706867112437)
                ·
                  refine ⟨239573927273972518791791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2555455224255706867112437 239573927273972518791791)
                  ·
                    rfl

theorem cell23_4199117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_4199117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199117 prefixEnd_4199117 := by exact prefixLift 4199117
  have htrace : WordTrace (prefixWord ++ tailWord_4199117) baseStart_4199117 baseEnd_4199117 := by
    simpa [prefixWord, tailWord_4199117, baseEnd_4199117] using wordTrace_append hprefix tailTrace_4199117
  have hstable : (prefixWord ++ tailWord_4199117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199117).length < 2 ^ (prefixWord ++ tailWord_4199117).sum := by decide
  have hdescent : baseEnd_4199117 < baseStart_4199117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199209 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 3, 1, 5]
def baseStart_4199209 : Nat := 118140960795 + 4199209 * 2 ^ 59
def prefixEnd_4199209 : Nat := 4983230072969 + 3 ^ 40 * 4199209 * 2
def baseEnd_4199209 : Nat := 2156212585685966309175695

theorem tailTrace_4199209 : CollatzResearch.WordTrace tailWord_4199209 prefixEnd_4199209 2156212585685966309175695 := by
  unfold tailWord_4199209
  simp only [CollatzResearch.WordTrace]
  refine ⟨153157734643990435645664681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102105156429326957097109787 153157734643990435645664681)
  ·
    refine ⟨114868300982992826734248511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153157734643990435645664681 114868300982992826734248511)
    ·
      refine ⟨172302451474489240101372767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114868300982992826734248511 172302451474489240101372767)
      ·
        refine ⟨258453677211733860152059151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172302451474489240101372767 258453677211733860152059151)
        ·
          refine ⟨387680515817600790228088727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258453677211733860152059151 387680515817600790228088727)
          ·
            refine ⟨581520773726401185342133091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387680515817600790228088727 581520773726401185342133091)
            ·
              refine ⟨872281160589601778013199637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581520773726401185342133091 872281160589601778013199637)
              ·
                refine ⟨40888179402637583344368733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 872281160589601778013199637 40888179402637583344368733)
                ·
                  refine ⟨15333067275989093754138275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40888179402637583344368733 15333067275989093754138275)
                  ·
                    refine ⟨22999600913983640631207413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15333067275989093754138275 22999600913983640631207413)
                    ·
                      refine ⟨2156212585685966309175695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22999600913983640631207413 2156212585685966309175695)
                      ·
                        rfl

theorem cell23_4199209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 1, 5].length) (baseStart_4199209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199209 prefixEnd_4199209 := by exact prefixLift 4199209
  have htrace : WordTrace (prefixWord ++ tailWord_4199209) baseStart_4199209 baseEnd_4199209 := by
    simpa [prefixWord, tailWord_4199209, baseEnd_4199209] using wordTrace_append hprefix tailTrace_4199209
  have hstable : (prefixWord ++ tailWord_4199209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199209).length < 2 ^ (prefixWord ++ tailWord_4199209).sum := by decide
  have hdescent : baseEnd_4199209 < baseStart_4199209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199220 : List Nat := [2, 5, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_4199220 : Nat := 118140960795 + 4199220 * 2 ^ 59
def prefixEnd_4199220 : Nat := 4983230072969 + 3 ^ 40 * 4199220 * 2
def baseEnd_4199220 : Nat := 718739411324388588712715

theorem tailTrace_4199220 : CollatzResearch.WordTrace tailWord_4199220 prefixEnd_4199220 718739411324388588712715 := by
  unfold tailWord_4199220
  simp only [CollatzResearch.WordTrace]
  refine ⟨76579067923475292262157557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102105423897967056349543409 76579067923475292262157557)
  ·
    refine ⟨7179287617825808649577271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76579067923475292262157557 7179287617825808649577271)
    ·
      refine ⟨10768931426738712974365907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7179287617825808649577271 10768931426738712974365907)
      ·
        refine ⟨16153397140108069461548861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10768931426738712974365907 16153397140108069461548861)
        ·
          refine ⟨6057523927540526048080823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16153397140108069461548861 6057523927540526048080823)
          ·
            refine ⟨9086285891310789072121235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6057523927540526048080823 9086285891310789072121235)
            ·
              refine ⟨13629428836966183608181853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9086285891310789072121235 13629428836966183608181853)
              ·
                refine ⟨5111035813862318853068195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13629428836966183608181853 5111035813862318853068195)
                ·
                  refine ⟨7666553720793478279602293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5111035813862318853068195 7666553720793478279602293)
                  ·
                    refine ⟨718739411324388588712715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7666553720793478279602293 718739411324388588712715)
                    ·
                      rfl

theorem cell23_4199220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_4199220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199220 prefixEnd_4199220 := by exact prefixLift 4199220
  have htrace : WordTrace (prefixWord ++ tailWord_4199220) baseStart_4199220 baseEnd_4199220 := by
    simpa [prefixWord, tailWord_4199220, baseEnd_4199220] using wordTrace_append hprefix tailTrace_4199220
  have hstable : (prefixWord ++ tailWord_4199220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199220).length < 2 ^ (prefixWord ++ tailWord_4199220).sum := by decide
  have hdescent : baseEnd_4199220 < baseStart_4199220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199223 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 5, 2, 2]
def baseStart_4199223 : Nat := 118140960795 + 4199223 * 2 ^ 59
def prefixEnd_4199223 : Nat := 4983230072969 + 3 ^ 40 * 4199223 * 2
def baseEnd_4199223 : Nat := 2156219774415129254400631

theorem tailTrace_4199223 : CollatzResearch.WordTrace tailWord_4199223 prefixEnd_4199223 2156219774415129254400631 := by
  unfold tailWord_4199223
  simp only [CollatzResearch.WordTrace]
  refine ⟨153158245265939716036674323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102105496843959810691116215 153158245265939716036674323)
  ·
    refine ⟨229737367898909574055011485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153158245265939716036674323 229737367898909574055011485)
    ·
      refine ⟨86151512962091090270629307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229737367898909574055011485 86151512962091090270629307)
      ·
        refine ⟨129227269443136635405943961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86151512962091090270629307 129227269443136635405943961)
        ·
          refine ⟨96920452082352476554457971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129227269443136635405943961 96920452082352476554457971)
          ·
            refine ⟨145380678123528714831686957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96920452082352476554457971 145380678123528714831686957)
            ·
              refine ⟨54517754296323268061882609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145380678123528714831686957 54517754296323268061882609)
              ·
                refine ⟨40888315722242451046411957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54517754296323268061882609 40888315722242451046411957)
                ·
                  refine ⟨3833279598960229785601121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40888315722242451046411957 3833279598960229785601121)
                  ·
                    refine ⟨2874959699220172339200841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3833279598960229785601121 2874959699220172339200841)
                    ·
                      refine ⟨2156219774415129254400631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2874959699220172339200841 2156219774415129254400631)
                      ·
                        rfl

theorem cell23_4199223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5, 2, 2].length) (baseStart_4199223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199223 prefixEnd_4199223 := by exact prefixLift 4199223
  have htrace : WordTrace (prefixWord ++ tailWord_4199223) baseStart_4199223 baseEnd_4199223 := by
    simpa [prefixWord, tailWord_4199223, baseEnd_4199223] using wordTrace_append hprefix tailTrace_4199223
  have hstable : (prefixWord ++ tailWord_4199223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199223).length < 2 ^ (prefixWord ++ tailWord_4199223).sum := by decide
  have hdescent : baseEnd_4199223 < baseStart_4199223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199239 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 7]
def baseStart_4199239 : Nat := 118140960795 + 4199239 * 2 ^ 59
def prefixEnd_4199239 : Nat := 4983230072969 + 3 ^ 40 * 4199239 * 2
def baseEnd_4199239 : Nat := 2156227990105601191800557

theorem tailTrace_4199239 : CollatzResearch.WordTrace tailWord_4199239 prefixEnd_4199239 2156227990105601191800557 := by
  unfold tailWord_4199239
  simp only [CollatzResearch.WordTrace]
  refine ⟨153158828833881750769256771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102105885889254500512837847 153158828833881750769256771)
  ·
    refine ⟨229738243250822626153885157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153158828833881750769256771 229738243250822626153885157)
    ·
      refine ⟨43075920609529242403853467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229738243250822626153885157 43075920609529242403853467)
      ·
        refine ⟨64613880914293863605780201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43075920609529242403853467 64613880914293863605780201)
        ·
          refine ⟨48460410685720397704335151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64613880914293863605780201 48460410685720397704335151)
          ·
            refine ⟨72690616028580596556502727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48460410685720397704335151 72690616028580596556502727)
            ·
              refine ⟨109035924042870894834754091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72690616028580596556502727 109035924042870894834754091)
              ·
                refine ⟨163553886064306342252131137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109035924042870894834754091 163553886064306342252131137)
                ·
                  refine ⟨122665414548229756689098353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163553886064306342252131137 122665414548229756689098353)
                  ·
                    refine ⟨91999060911172317516823765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 122665414548229756689098353 91999060911172317516823765)
                    ·
                      refine ⟨2156227990105601191800557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91999060911172317516823765 2156227990105601191800557)
                      ·
                        rfl

theorem cell23_4199239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_4199239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199239 prefixEnd_4199239 := by exact prefixLift 4199239
  have htrace : WordTrace (prefixWord ++ tailWord_4199239) baseStart_4199239 baseEnd_4199239 := by
    simpa [prefixWord, tailWord_4199239, baseEnd_4199239] using wordTrace_append hprefix tailTrace_4199239
  have hstable : (prefixWord ++ tailWord_4199239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199239).length < 2 ^ (prefixWord ++ tailWord_4199239).sum := by decide
  have hdescent : baseEnd_4199239 < baseStart_4199239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199240 : List Nat := [2, 1, 3, 1, 1, 3, 4, 1, 3, 2, 2]
def baseStart_4199240 : Nat := 118140960795 + 4199240 * 2 ^ 59
def prefixEnd_4199240 : Nat := 4983230072969 + 3 ^ 40 * 4199240 * 2
def baseEnd_4199240 : Nat := 2156228503586255687888053

theorem tailTrace_4199240 : CollatzResearch.WordTrace tailWord_4199240 prefixEnd_4199240 2156228503586255687888053 := by
  unfold tailWord_4199240
  simp only [CollatzResearch.WordTrace]
  refine ⟨76579432653439063970021587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102105910204585418626695449 76579432653439063970021587)
  ·
    refine ⟨114869148980158595955032381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76579432653439063970021587 114869148980158595955032381)
    ·
      refine ⟨43075930867559473483137143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114869148980158595955032381 43075930867559473483137143)
      ·
        refine ⟨64613896301339210224705715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43075930867559473483137143 64613896301339210224705715)
        ·
          refine ⟨96920844452008815337058573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64613896301339210224705715 96920844452008815337058573)
          ·
            refine ⟨36345316669503305751396965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96920844452008815337058573 36345316669503305751396965)
            ·
              refine ⟨6814746875531869828386931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36345316669503305751396965 6814746875531869828386931)
              ·
                refine ⟨10222120313297804742580397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6814746875531869828386931 10222120313297804742580397)
                ·
                  refine ⟨3833295117486676778467649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10222120313297804742580397 3833295117486676778467649)
                  ·
                    refine ⟨2874971338115007583850737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3833295117486676778467649 2874971338115007583850737)
                    ·
                      refine ⟨2156228503586255687888053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2874971338115007583850737 2156228503586255687888053)
                      ·
                        rfl

theorem cell23_4199240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 3, 2, 2].length) (baseStart_4199240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199240 prefixEnd_4199240 := by exact prefixLift 4199240
  have htrace : WordTrace (prefixWord ++ tailWord_4199240) baseStart_4199240 baseEnd_4199240 := by
    simpa [prefixWord, tailWord_4199240, baseEnd_4199240] using wordTrace_append hprefix tailTrace_4199240
  have hstable : (prefixWord ++ tailWord_4199240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199240).length < 2 ^ (prefixWord ++ tailWord_4199240).sum := by decide
  have hdescent : baseEnd_4199240 < baseStart_4199240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199250 : List Nat := [3, 2, 2, 1, 1, 2, 5, 1, 2, 4]
def baseStart_4199250 : Nat := 118140960795 + 4199250 * 2 ^ 59
def prefixEnd_4199250 : Nat := 4983230072969 + 3 ^ 40 * 4199250 * 2
def baseEnd_4199250 : Nat := 718744546130933549587669

theorem tailTrace_4199250 : CollatzResearch.WordTrace tailWord_4199250 prefixEnd_4199250 718744546130933549587669 := by
  unfold tailWord_4199250
  simp only [CollatzResearch.WordTrace]
  refine ⟨38289807509210474911976801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102106153357894599765271469 38289807509210474911976801)
  ·
    refine ⟨28717355631907856183982601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38289807509210474911976801 28717355631907856183982601)
    ·
      refine ⟨21538016723930892137986951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28717355631907856183982601 21538016723930892137986951)
      ·
        refine ⟨32307025085896338206980427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21538016723930892137986951 32307025085896338206980427)
        ·
          refine ⟨48460537628844507310470641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32307025085896338206980427 48460537628844507310470641)
          ·
            refine ⟨36345403221633380482852981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48460537628844507310470641 36345403221633380482852981)
            ·
              refine ⟨3407381552028129420267467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36345403221633380482852981 3407381552028129420267467)
              ·
                refine ⟨5111072328042194130401201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3407381552028129420267467 5111072328042194130401201)
                ·
                  refine ⟨3833304246031645597800901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5111072328042194130401201 3833304246031645597800901)
                  ·
                    refine ⟨718744546130933549587669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3833304246031645597800901 718744546130933549587669)
                    ·
                      rfl

theorem cell23_4199250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_4199250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199250 prefixEnd_4199250 := by exact prefixLift 4199250
  have htrace : WordTrace (prefixWord ++ tailWord_4199250) baseStart_4199250 baseEnd_4199250 := by
    simpa [prefixWord, tailWord_4199250, baseEnd_4199250] using wordTrace_append hprefix tailTrace_4199250
  have hstable : (prefixWord ++ tailWord_4199250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199250).length < 2 ^ (prefixWord ++ tailWord_4199250).sum := by decide
  have hdescent : baseEnd_4199250 < baseStart_4199250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199260 : List Nat := [2, 2, 4, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_4199260 : Nat := 118140960795 + 4199260 * 2 ^ 59
def prefixEnd_4199260 : Nat := 4983230072969 + 3 ^ 40 * 4199260 * 2
def baseEnd_4199260 : Nat := 2156238773199345609637961

theorem tailTrace_4199260 : CollatzResearch.WordTrace tailWord_4199260 prefixEnd_4199260 2156238773199345609637961 := by
  unfold tailWord_4199260
  simp only [CollatzResearch.WordTrace]
  refine ⟨76579797383402835677885617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102106396511203780903847489 76579797383402835677885617)
  ·
    refine ⟨57434848037552126758414213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76579797383402835677885617 57434848037552126758414213)
    ·
      refine ⟨10769034007041023767202665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57434848037552126758414213 10769034007041023767202665)
      ·
        refine ⟨8076775505280767825401999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10769034007041023767202665 8076775505280767825401999)
        ·
          refine ⟨12115163257921151738102999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8076775505280767825401999 12115163257921151738102999)
          ·
            refine ⟨18172744886881727607154499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12115163257921151738102999 18172744886881727607154499)
            ·
              refine ⟨27259117330322591410731749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18172744886881727607154499 27259117330322591410731749)
              ·
                refine ⟨5111084499435485889512203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27259117330322591410731749 5111084499435485889512203)
                ·
                  refine ⟨7666626749153228834268305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5111084499435485889512203 7666626749153228834268305)
                  ·
                    refine ⟨5749970061864921625701229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7666626749153228834268305 5749970061864921625701229)
                    ·
                      refine ⟨2156238773199345609637961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5749970061864921625701229 2156238773199345609637961)
                      ·
                        rfl

theorem cell23_4199260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_4199260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199260 prefixEnd_4199260 := by exact prefixLift 4199260
  have htrace : WordTrace (prefixWord ++ tailWord_4199260) baseStart_4199260 baseEnd_4199260 := by
    simpa [prefixWord, tailWord_4199260, baseEnd_4199260] using wordTrace_append hprefix tailTrace_4199260
  have hstable : (prefixWord ++ tailWord_4199260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199260).length < 2 ^ (prefixWord ++ tailWord_4199260).sum := by decide
  have hdescent : baseEnd_4199260 < baseStart_4199260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199279 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 8]
def baseStart_4199279 : Nat := 118140960795 + 4199279 * 2 ^ 59
def prefixEnd_4199279 : Nat := 4983230072969 + 3 ^ 40 * 4199279 * 2
def baseEnd_4199279 : Nat := 2156248529331781035300373

theorem tailTrace_4199279 : CollatzResearch.WordTrace tailWord_4199279 prefixEnd_4199279 2156248529331781035300373 := by
  unfold tailWord_4199279
  simp only [CollatzResearch.WordTrace]
  refine ⟨153160287753736837600712891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102106858502491225067141927 153160287753736837600712891)
  ·
    refine ⟨229740431630605256401069337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153160287753736837600712891 229740431630605256401069337)
    ·
      refine ⟨172305323722953942300802003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229740431630605256401069337 172305323722953942300802003)
      ·
        refine ⟨258457985584430913451203005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172305323722953942300802003 258457985584430913451203005)
        ·
          refine ⟨96921744594161592544201127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 258457985584430913451203005 96921744594161592544201127)
          ·
            refine ⟨145382616891242388816301691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96921744594161592544201127 145382616891242388816301691)
            ·
              refine ⟨218073925336863583224452537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145382616891242388816301691 218073925336863583224452537)
              ·
                refine ⟨163555444002647687418339403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218073925336863583224452537 163555444002647687418339403)
                ·
                  refine ⟨245333166003971531127509105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163555444002647687418339403 245333166003971531127509105)
                  ·
                    refine ⟨183999874502978648345631829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 245333166003971531127509105 183999874502978648345631829)
                    ·
                      refine ⟨2156248529331781035300373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 183999874502978648345631829 2156248529331781035300373)
                      ·
                        rfl

theorem cell23_4199279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_4199279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199279 prefixEnd_4199279 := by exact prefixLift 4199279
  have htrace : WordTrace (prefixWord ++ tailWord_4199279) baseStart_4199279 baseEnd_4199279 := by
    simpa [prefixWord, tailWord_4199279, baseEnd_4199279] using wordTrace_append hprefix tailTrace_4199279
  have hstable : (prefixWord ++ tailWord_4199279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199279).length < 2 ^ (prefixWord ++ tailWord_4199279).sum := by decide
  have hdescent : baseEnd_4199279 < baseStart_4199279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199313 : List Nat := [1, 2, 2, 1, 1, 1, 3, 5, 1, 4, 2]
def baseStart_4199313 : Nat := 118140960795 + 4199313 * 2 ^ 59
def prefixEnd_4199313 : Nat := 4983230072969 + 3 ^ 40 * 4199313 * 2
def baseEnd_4199313 : Nat := 2156265987674033902275217

theorem tailTrace_4199313 : CollatzResearch.WordTrace tailWord_4199313 prefixEnd_4199313 2156265987674033902275217 := by
  unfold tailWord_4199313
  simp only [CollatzResearch.WordTrace]
  refine ⟨153161527835613661407450593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102107685223742440938300395 153161527835613661407450593)
  ·
    refine ⟨114871145876710246055587945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153161527835613661407450593 114871145876710246055587945)
    ·
      refine ⟨86153359407532684541690959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114871145876710246055587945 86153359407532684541690959)
      ·
        refine ⟨129230039111299026812536439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86153359407532684541690959 129230039111299026812536439)
        ·
          refine ⟨193845058666948540218804659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129230039111299026812536439 193845058666948540218804659)
          ·
            refine ⟨290767588000422810328206989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193845058666948540218804659 290767588000422810328206989)
            ·
              refine ⟨109037845500158553873077621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290767588000422810328206989 109037845500158553873077621)
              ·
                refine ⟨10222298015639864425601027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109037845500158553873077621 10222298015639864425601027)
                ·
                  refine ⟨15333447023459796638401541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10222298015639864425601027 15333447023459796638401541)
                  ·
                    refine ⟨2875021316898711869700289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15333447023459796638401541 2875021316898711869700289)
                    ·
                      refine ⟨2156265987674033902275217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2875021316898711869700289 2156265987674033902275217)
                      ·
                        rfl

theorem cell23_4199313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 4, 2].length) (baseStart_4199313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199313 prefixEnd_4199313 := by exact prefixLift 4199313
  have htrace : WordTrace (prefixWord ++ tailWord_4199313) baseStart_4199313 baseEnd_4199313 := by
    simpa [prefixWord, tailWord_4199313, baseEnd_4199313] using wordTrace_append hprefix tailTrace_4199313
  have hstable : (prefixWord ++ tailWord_4199313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199313).length < 2 ^ (prefixWord ++ tailWord_4199313).sum := by decide
  have hdescent : baseEnd_4199313 < baseStart_4199313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199317 : List Nat := [1, 3, 2, 1, 1, 6, 1, 2, 1, 3, 2]
def baseStart_4199317 : Nat := 118140960795 + 4199317 * 2 ^ 59
def prefixEnd_4199317 : Nat := 4983230072969 + 3 ^ 40 * 4199317 * 2
def baseEnd_4199317 : Nat := 2156268041596651886625199

theorem tailTrace_4199317 : CollatzResearch.WordTrace tailWord_4199317 prefixEnd_4199317 2156268041596651886625199 := by
  unfold tailWord_4199317
  simp only [CollatzResearch.WordTrace]
  refine ⟨153161673727599170090596205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102107782485066113393730803 153161673727599170090596205)
  ·
    refine ⟨57435627647849688783973577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153161673727599170090596205 57435627647849688783973577)
    ·
      refine ⟨43076720735887266587980183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57435627647849688783973577 43076720735887266587980183)
      ·
        refine ⟨64615081103830899881970275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43076720735887266587980183 64615081103830899881970275)
        ·
          refine ⟨96922621655746349822955413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64615081103830899881970275 96922621655746349822955413)
          ·
            refine ⟨4543247890113110147951035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 96922621655746349822955413 4543247890113110147951035)
            ·
              refine ⟨6814871835169665221926553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4543247890113110147951035 6814871835169665221926553)
              ·
                refine ⟨5111153876377248916444915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6814871835169665221926553 5111153876377248916444915)
                ·
                  refine ⟨7666730814565873374667373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5111153876377248916444915 7666730814565873374667373)
                  ·
                    refine ⟨2875024055462202515500265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7666730814565873374667373 2875024055462202515500265)
                    ·
                      refine ⟨2156268041596651886625199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2875024055462202515500265 2156268041596651886625199)
                      ·
                        rfl

theorem cell23_4199317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 3, 2].length) (baseStart_4199317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199317 prefixEnd_4199317 := by exact prefixLift 4199317
  have htrace : WordTrace (prefixWord ++ tailWord_4199317) baseStart_4199317 baseEnd_4199317 := by
    simpa [prefixWord, tailWord_4199317, baseEnd_4199317] using wordTrace_append hprefix tailTrace_4199317
  have hstable : (prefixWord ++ tailWord_4199317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199317).length < 2 ^ (prefixWord ++ tailWord_4199317).sum := by decide
  have hdescent : baseEnd_4199317 < baseStart_4199317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199330 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 3, 4, 2]
def baseStart_4199330 : Nat := 118140960795 + 4199330 * 2 ^ 59
def prefixEnd_4199330 : Nat := 4983230072969 + 3 ^ 40 * 4199330 * 2
def baseEnd_4199330 : Nat := 2156274716845160335762639

theorem tailTrace_4199330 : CollatzResearch.WordTrace tailWord_4199330 prefixEnd_4199330 2156274716845160335762639 := by
  unfold tailWord_4199330
  simp only [CollatzResearch.WordTrace]
  refine ⟨38290536969138018327704861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102108098584368048873879629 38290536969138018327704861)
  ·
    refine ⟨14358951363426756872889323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38290536969138018327704861 14358951363426756872889323)
    ·
      refine ⟨21538427045140135309333985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14358951363426756872889323 21538427045140135309333985)
      ·
        refine ⟨16153820283855101482000489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21538427045140135309333985 16153820283855101482000489)
        ·
          refine ⟨12115365212891326111500367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16153820283855101482000489 12115365212891326111500367)
          ·
            refine ⟨18173047819336989167250551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12115365212891326111500367 18173047819336989167250551)
            ·
              refine ⟨27259571729005483750875827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18173047819336989167250551 27259571729005483750875827)
              ·
                refine ⟨40889357593508225626313741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27259571729005483750875827 40889357593508225626313741)
                ·
                  refine ⟨15333509097565584609867653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40889357593508225626313741 15333509097565584609867653)
                  ·
                    refine ⟨2875032955793547114350185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15333509097565584609867653 2875032955793547114350185)
                    ·
                      refine ⟨2156274716845160335762639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2875032955793547114350185 2156274716845160335762639)
                      ·
                        rfl

theorem cell23_4199330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_4199330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199330 prefixEnd_4199330 := by exact prefixLift 4199330
  have htrace : WordTrace (prefixWord ++ tailWord_4199330) baseStart_4199330 baseEnd_4199330 := by
    simpa [prefixWord, tailWord_4199330, baseEnd_4199330] using wordTrace_append hprefix tailTrace_4199330
  have hstable : (prefixWord ++ tailWord_4199330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199330).length < 2 ^ (prefixWord ++ tailWord_4199330).sum := by decide
  have hdescent : baseEnd_4199330 < baseStart_4199330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199364 : List Nat := [2, 3, 3, 3, 1, 1, 2, 1, 1, 4, 2]
def baseStart_4199364 : Nat := 118140960795 + 4199364 * 2 ^ 59
def prefixEnd_4199364 : Nat := 4983230072969 + 3 ^ 40 * 4199364 * 2
def baseEnd_4199364 : Nat := 2156292175187413202737483

theorem tailTrace_4199364 : CollatzResearch.WordTrace tailWord_4199364 prefixEnd_4199364 2156292175187413202737483 := by
  unfold tailWord_4199364
  simp only [CollatzResearch.WordTrace]
  refine ⟨76581693979214448558778573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102108925305619264745038097 76581693979214448558778573)
  ·
    refine ⟨28718135242205418209541965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76581693979214448558778573 28718135242205418209541965)
    ·
      refine ⟨10769300715827031828578237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28718135242205418209541965 10769300715827031828578237)
      ·
        refine ⟨4038487768435136935716839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10769300715827031828578237 4038487768435136935716839)
        ·
          refine ⟨6057731652652705403575259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4038487768435136935716839 6057731652652705403575259)
          ·
            refine ⟨9086597478979058105362889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6057731652652705403575259 9086597478979058105362889)
            ·
              refine ⟨6814948109234293579022167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9086597478979058105362889 6814948109234293579022167)
              ·
                refine ⟨10222422163851440368533251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6814948109234293579022167 10222422163851440368533251)
                ·
                  refine ⟨15333633245777160552799877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10222422163851440368533251 15333633245777160552799877)
                  ·
                    refine ⟨2875056233583217603649977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15333633245777160552799877 2875056233583217603649977)
                    ·
                      refine ⟨2156292175187413202737483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2875056233583217603649977 2156292175187413202737483)
                      ·
                        rfl

theorem cell23_4199364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_4199364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199364 prefixEnd_4199364 := by exact prefixLift 4199364
  have htrace : WordTrace (prefixWord ++ tailWord_4199364) baseStart_4199364 baseEnd_4199364 := by
    simpa [prefixWord, tailWord_4199364, baseEnd_4199364] using wordTrace_append hprefix tailTrace_4199364
  have hstable : (prefixWord ++ tailWord_4199364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199364).length < 2 ^ (prefixWord ++ tailWord_4199364).sum := by decide
  have hdescent : baseEnd_4199364 < baseStart_4199364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199416 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 4, 1, 6]
def baseStart_4199416 : Nat := 118140960795 + 4199416 * 2 ^ 59
def prefixEnd_4199416 : Nat := 4983230072969 + 3 ^ 40 * 4199416 * 2
def baseEnd_4199416 : Nat := 2156318876181446999287243

theorem tailTrace_4199416 : CollatzResearch.WordTrace tailWord_4199416 prefixEnd_4199416 2156318876181446999287243 := by
  unfold tailWord_4199416
  simp only [CollatzResearch.WordTrace]
  refine ⟨76582642277120254999225051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102110189702827006665633401 76582642277120254999225051)
  ·
    refine ⟨114873963415680382498837577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76582642277120254999225051 114873963415680382498837577)
    ·
      refine ⟨86155472561760286874128183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114873963415680382498837577 86155472561760286874128183)
      ·
        refine ⟨129233208842640430311192275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86155472561760286874128183 129233208842640430311192275)
        ·
          refine ⟨193849813263960645466788413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129233208842640430311192275 193849813263960645466788413)
          ·
            refine ⟨72693679973985242050045655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193849813263960645466788413 72693679973985242050045655)
            ·
              refine ⟨109040519960977863075068483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72693679973985242050045655 109040519960977863075068483)
              ·
                refine ⟨163560779941466794612602725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109040519960977863075068483 163560779941466794612602725)
                ·
                  refine ⟨30667646239025023989863011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163560779941466794612602725 30667646239025023989863011)
                  ·
                    refine ⟨46001469358537535984794517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30667646239025023989863011 46001469358537535984794517)
                    ·
                      refine ⟨2156318876181446999287243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46001469358537535984794517 2156318876181446999287243)
                      ·
                        rfl

theorem cell23_4199416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_4199416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199416 prefixEnd_4199416 := by exact prefixLift 4199416
  have htrace : WordTrace (prefixWord ++ tailWord_4199416) baseStart_4199416 baseEnd_4199416 := by
    simpa [prefixWord, tailWord_4199416, baseEnd_4199416] using wordTrace_append hprefix tailTrace_4199416
  have hstable : (prefixWord ++ tailWord_4199416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199416).length < 2 ^ (prefixWord ++ tailWord_4199416).sum := by decide
  have hdescent : baseEnd_4199416 < baseStart_4199416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199420 : List Nat := [2, 2, 2, 1, 2, 3, 2, 1, 2, 4, 2]
def baseStart_4199420 : Nat := 118140960795 + 4199420 * 2 ^ 59
def prefixEnd_4199420 : Nat := 4983230072969 + 3 ^ 40 * 4199420 * 2
def baseEnd_4199420 : Nat := 2156320930104064983637225

theorem tailTrace_4199420 : CollatzResearch.WordTrace tailWord_4199420 prefixEnd_4199420 2156320930104064983637225 := by
  unfold tailWord_4199420
  simp only [CollatzResearch.WordTrace]
  refine ⟨76582715223113009340797857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102110286964150679121063809 76582715223113009340797857)
  ·
    refine ⟨57437036417334757005598393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76582715223113009340797857 57437036417334757005598393)
    ·
      refine ⟨43077777313001067754198795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57437036417334757005598393 43077777313001067754198795)
      ·
        refine ⟨64616665969501601631298193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43077777313001067754198795 64616665969501601631298193)
        ·
          refine ⟨48462499477126201223473645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64616665969501601631298193 48462499477126201223473645)
          ·
            refine ⟨18173437303922325458802617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48462499477126201223473645 18173437303922325458802617)
            ·
              refine ⟨13630077977941744094101963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18173437303922325458802617 13630077977941744094101963)
              ·
                refine ⟨20445116966912616141152945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13630077977941744094101963 20445116966912616141152945)
                ·
                  refine ⟨15333837725184462105864709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20445116966912616141152945 15333837725184462105864709)
                  ·
                    refine ⟨2875094573472086644849633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15333837725184462105864709 2875094573472086644849633)
                    ·
                      refine ⟨2156320930104064983637225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2875094573472086644849633 2156320930104064983637225)
                      ·
                        rfl

theorem cell23_4199420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 2, 4, 2].length) (baseStart_4199420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199420 prefixEnd_4199420 := by exact prefixLift 4199420
  have htrace : WordTrace (prefixWord ++ tailWord_4199420) baseStart_4199420 baseEnd_4199420 := by
    simpa [prefixWord, tailWord_4199420, baseEnd_4199420] using wordTrace_append hprefix tailTrace_4199420
  have hstable : (prefixWord ++ tailWord_4199420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199420).length < 2 ^ (prefixWord ++ tailWord_4199420).sum := by decide
  have hdescent : baseEnd_4199420 < baseStart_4199420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199473 : List Nat := [1, 2, 2, 3, 1, 2, 2, 2, 3, 5]
def baseStart_4199473 : Nat := 118140960795 + 4199473 * 2 ^ 59
def prefixEnd_4199473 : Nat := 4983230072969 + 3 ^ 40 * 4199473 * 2
def baseEnd_4199473 : Nat := 718782714859584425424827

theorem tailTrace_4199473 : CollatzResearch.WordTrace tailWord_4199473 prefixEnd_4199473 718782714859584425424827 := by
  unfold tailWord_4199473
  simp only [CollatzResearch.WordTrace]
  refine ⟨153167363515034008733275073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102111575676689339155516715 153167363515034008733275073)
  ·
    refine ⟨114875522636275506549956305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153167363515034008733275073 114875522636275506549956305)
    ·
      refine ⟨86156641977206629912467229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114875522636275506549956305 86156641977206629912467229)
      ·
        refine ⟨32308740741452486217175211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86156641977206629912467229 32308740741452486217175211)
        ·
          refine ⟨48463111112178729325762817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32308740741452486217175211 48463111112178729325762817)
          ·
            refine ⟨36347333334134046994322113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48463111112178729325762817 36347333334134046994322113)
            ·
              refine ⟨27260500000600535245741585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36347333334134046994322113 27260500000600535245741585)
              ·
                refine ⟨20445375000450401434306189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27260500000600535245741585 20445375000450401434306189)
                ·
                  refine ⟨7667015625168900537864821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20445375000450401434306189 7667015625168900537864821)
                  ·
                    refine ⟨718782714859584425424827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7667015625168900537864821 718782714859584425424827)
                    ·
                      rfl

theorem cell23_4199473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 5].length) (baseStart_4199473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199473 prefixEnd_4199473 := by exact prefixLift 4199473
  have htrace : WordTrace (prefixWord ++ tailWord_4199473) baseStart_4199473 baseEnd_4199473 := by
    simpa [prefixWord, tailWord_4199473, baseEnd_4199473] using wordTrace_append hprefix tailTrace_4199473
  have hstable : (prefixWord ++ tailWord_4199473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199473).length < 2 ^ (prefixWord ++ tailWord_4199473).sum := by decide
  have hdescent : baseEnd_4199473 < baseStart_4199473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199513 : List Nat := [1, 2, 1, 2, 2, 1, 2, 5, 1, 1, 5]
def baseStart_4199513 : Nat := 118140960795 + 4199513 * 2 ^ 59
def prefixEnd_4199513 : Nat := 4983230072969 + 3 ^ 40 * 4199513 * 2
def baseEnd_4199513 : Nat := 2156368683804933119774297

theorem tailTrace_4199513 : CollatzResearch.WordTrace tailWord_4199513 prefixEnd_4199513 2156368683804933119774297 := by
  unfold tailWord_4199513
  simp only [CollatzResearch.WordTrace]
  refine ⟨153168822434889095564731193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102112548289926063709820795 153168822434889095564731193)
  ·
    refine ⟨114876616826166821673548395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153168822434889095564731193 114876616826166821673548395)
    ·
      refine ⟨172314925239250232510322593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114876616826166821673548395 172314925239250232510322593)
      ·
        refine ⟨129236193929437674382741945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172314925239250232510322593 129236193929437674382741945)
        ·
          refine ⟨96927145447078255787056459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129236193929437674382741945 96927145447078255787056459)
          ·
            refine ⟨145390718170617383680584689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96927145447078255787056459 145390718170617383680584689)
            ·
              refine ⟨109043038627963037760438517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145390718170617383680584689 109043038627963037760438517)
              ·
                refine ⟨10222784871371534790041111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109043038627963037760438517 10222784871371534790041111)
                ·
                  refine ⟨15334177307057302185061667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10222784871371534790041111 15334177307057302185061667)
                  ·
                    refine ⟨23001265960585953277592501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15334177307057302185061667 23001265960585953277592501)
                    ·
                      refine ⟨2156368683804933119774297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23001265960585953277592501 2156368683804933119774297)
                      ·
                        rfl

theorem cell23_4199513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_4199513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199513 prefixEnd_4199513 := by exact prefixLift 4199513
  have htrace : WordTrace (prefixWord ++ tailWord_4199513) baseStart_4199513 baseEnd_4199513 := by
    simpa [prefixWord, tailWord_4199513, baseEnd_4199513] using wordTrace_append hprefix tailTrace_4199513
  have hstable : (prefixWord ++ tailWord_4199513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199513).length < 2 ^ (prefixWord ++ tailWord_4199513).sum := by decide
  have hdescent : baseEnd_4199513 < baseStart_4199513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199523 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 4]
def baseStart_4199523 : Nat := 118140960795 + 4199523 * 2 ^ 59
def prefixEnd_4199523 : Nat := 4983230072969 + 3 ^ 40 * 4199523 * 2
def baseEnd_4199523 : Nat := 2156373818611478080649251

theorem tailTrace_4199523 : CollatzResearch.WordTrace tailWord_4199523 prefixEnd_4199523 2156373818611478080649251 := by
  unfold tailWord_4199523
  simp only [CollatzResearch.WordTrace]
  refine ⟨153169187164852867272595223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102112791443235244848396815 153169187164852867272595223)
  ·
    refine ⟨229753780747279300908892835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153169187164852867272595223 229753780747279300908892835)
    ·
      refine ⟨344630671120918951363339253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229753780747279300908892835 344630671120918951363339253)
      ·
        refine ⟨32309125417586151690313055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 344630671120918951363339253 32309125417586151690313055)
        ·
          refine ⟨48463688126379227535469583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32309125417586151690313055 48463688126379227535469583)
          ·
            refine ⟨72695532189568841303204375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48463688126379227535469583 72695532189568841303204375)
            ·
              refine ⟨109043298284353261954806563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72695532189568841303204375 109043298284353261954806563)
              ·
                refine ⟨163564947426529892932209845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109043298284353261954806563 163564947426529892932209845)
                ·
                  refine ⟨15334213821237177462394673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 163564947426529892932209845 15334213821237177462394673)
                  ·
                    refine ⟨11500660365927883096796005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15334213821237177462394673 11500660365927883096796005)
                    ·
                      refine ⟨2156373818611478080649251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11500660365927883096796005 2156373818611478080649251)
                      ·
                        rfl

theorem cell23_4199523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_4199523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199523 prefixEnd_4199523 := by exact prefixLift 4199523
  have htrace : WordTrace (prefixWord ++ tailWord_4199523) baseStart_4199523 baseEnd_4199523 := by
    simpa [prefixWord, tailWord_4199523, baseEnd_4199523] using wordTrace_append hprefix tailTrace_4199523
  have hstable : (prefixWord ++ tailWord_4199523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199523).length < 2 ^ (prefixWord ++ tailWord_4199523).sum := by decide
  have hdescent : baseEnd_4199523 < baseStart_4199523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199561 : List Nat := [1, 2, 1, 1, 4, 4, 2, 3, 1, 2, 2]
def baseStart_4199561 : Nat := 118140960795 + 4199561 * 2 ^ 59
def prefixEnd_4199561 : Nat := 4983230072969 + 3 ^ 40 * 4199561 * 2
def baseEnd_4199561 : Nat := 2156393330876348931974077

theorem tailTrace_4199561 : CollatzResearch.WordTrace tailWord_4199561 prefixEnd_4199561 2156393330876348931974077 := by
  unfold tailWord_4199561
  simp only [CollatzResearch.WordTrace]
  refine ⟨153170573138715199762478537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102113715425810133174985691 153170573138715199762478537)
  ·
    refine ⟨114877929854036399821858903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153170573138715199762478537 114877929854036399821858903)
    ·
      refine ⟨172316894781054599732788355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114877929854036399821858903 172316894781054599732788355)
      ·
        refine ⟨258475342171581899599182533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172316894781054599732788355 258475342171581899599182533)
        ·
          refine ⟨48464126657171606174846725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 258475342171581899599182533 48464126657171606174846725)
          ·
            refine ⟨9087023748219676157783761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48464126657171606174846725 9087023748219676157783761)
            ·
              refine ⟨6815267811164757118337821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9087023748219676157783761 6815267811164757118337821)
              ·
                refine ⟨2555725429186783919376683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6815267811164757118337821 2555725429186783919376683)
                ·
                  refine ⟨3833588143780175879065025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2555725429186783919376683 3833588143780175879065025)
                  ·
                    refine ⟨2875191107835131909298769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3833588143780175879065025 2875191107835131909298769)
                    ·
                      refine ⟨2156393330876348931974077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2875191107835131909298769 2156393330876348931974077)
                      ·
                        rfl

theorem cell23_4199561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3, 1, 2, 2].length) (baseStart_4199561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199561 prefixEnd_4199561 := by exact prefixLift 4199561
  have htrace : WordTrace (prefixWord ++ tailWord_4199561) baseStart_4199561 baseEnd_4199561 := by
    simpa [prefixWord, tailWord_4199561, baseEnd_4199561] using wordTrace_append hprefix tailTrace_4199561
  have hstable : (prefixWord ++ tailWord_4199561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199561).length < 2 ^ (prefixWord ++ tailWord_4199561).sum := by decide
  have hdescent : baseEnd_4199561 < baseStart_4199561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199573 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 4, 2, 5]
def baseStart_4199573 : Nat := 118140960795 + 4199573 * 2 ^ 59
def prefixEnd_4199573 : Nat := 4983230072969 + 3 ^ 40 * 4199573 * 2
def baseEnd_4199573 : Nat := 2156399492644202885024021

theorem tailTrace_4199573 : CollatzResearch.WordTrace tailWord_4199573 prefixEnd_4199573 2156399492644202885024021 := by
  unfold tailWord_4199573
  simp only [CollatzResearch.WordTrace]
  refine ⟨153171010814671725811915373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102114007209781150541276915 153171010814671725811915373)
  ·
    refine ⟨57439129055501897179468265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153171010814671725811915373 57439129055501897179468265)
    ·
      refine ⟨43079346791626422884601199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57439129055501897179468265 43079346791626422884601199)
      ·
        refine ⟨64619020187439634326901799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43079346791626422884601199 64619020187439634326901799)
        ·
          refine ⟨96928530281159451490352699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64619020187439634326901799 96928530281159451490352699)
          ·
            refine ⟨145392795421739177235529049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96928530281159451490352699 145392795421739177235529049)
            ·
              refine ⟨109044596566304382926646787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145392795421739177235529049 109044596566304382926646787)
              ·
                refine ⟨163566894849456574389970181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109044596566304382926646787 163566894849456574389970181)
                ·
                  refine ⟨30668792784273107698119409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163566894849456574389970181 30668792784273107698119409)
                  ·
                    refine ⟨23001594588204830773589557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30668792784273107698119409 23001594588204830773589557)
                    ·
                      refine ⟨2156399492644202885024021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23001594588204830773589557 2156399492644202885024021)
                      ·
                        rfl

theorem cell23_4199573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_4199573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199573 prefixEnd_4199573 := by exact prefixLift 4199573
  have htrace : WordTrace (prefixWord ++ tailWord_4199573) baseStart_4199573 baseEnd_4199573 := by
    simpa [prefixWord, tailWord_4199573, baseEnd_4199573] using wordTrace_append hprefix tailTrace_4199573
  have hstable : (prefixWord ++ tailWord_4199573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199573).length < 2 ^ (prefixWord ++ tailWord_4199573).sum := by decide
  have hdescent : baseEnd_4199573 < baseStart_4199573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199594 : List Nat := [3, 1, 5, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_4199594 : Nat := 118140960795 + 4199594 * 2 ^ 59
def prefixEnd_4199594 : Nat := 4983230072969 + 3 ^ 40 * 4199594 * 2
def baseEnd_4199594 : Nat := 2156410275737947302861425

theorem tailTrace_4199594 : CollatzResearch.WordTrace tailWord_4199594 prefixEnd_4199594 2156410275737947302861425 := by
  unfold tailWord_4199594
  simp only [CollatzResearch.WordTrace]
  refine ⟨38292944186898911599607459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102114517831730430932286557 38292944186898911599607459)
  ·
    refine ⟨57439416280348367399411189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38292944186898911599607459 57439416280348367399411189)
    ·
      refine ⟨5384945276282659443694799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57439416280348367399411189 5384945276282659443694799)
      ·
        refine ⟨8077417914423989165542199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5384945276282659443694799 8077417914423989165542199)
        ·
          refine ⟨12116126871635983748313299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8077417914423989165542199 12116126871635983748313299)
          ·
            refine ⟨18174190307453975622469949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12116126871635983748313299 18174190307453975622469949)
            ·
              refine ⟨6815321365295240858426231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18174190307453975622469949 6815321365295240858426231)
              ·
                refine ⟨10222982047942861287639347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6815321365295240858426231 10222982047942861287639347)
                ·
                  refine ⟨15334473071914291931459021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10222982047942861287639347 15334473071914291931459021)
                  ·
                    refine ⟨5750427401967859474297133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15334473071914291931459021 5750427401967859474297133)
                    ·
                      refine ⟨2156410275737947302861425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5750427401967859474297133 2156410275737947302861425)
                      ·
                        rfl

theorem cell23_4199594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_4199594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199594 prefixEnd_4199594 := by exact prefixLift 4199594
  have htrace : WordTrace (prefixWord ++ tailWord_4199594) baseStart_4199594 baseEnd_4199594 := by
    simpa [prefixWord, tailWord_4199594, baseEnd_4199594] using wordTrace_append hprefix tailTrace_4199594
  have hstable : (prefixWord ++ tailWord_4199594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199594).length < 2 ^ (prefixWord ++ tailWord_4199594).sum := by decide
  have hdescent : baseEnd_4199594 < baseStart_4199594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199623 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 9]
def baseStart_4199623 : Nat := 118140960795 + 4199623 * 2 ^ 59
def prefixEnd_4199623 : Nat := 4983230072969 + 3 ^ 40 * 4199623 * 2
def baseEnd_4199623 : Nat := 239602796297436409933199

theorem tailTrace_4199623 : CollatzResearch.WordTrace tailWord_4199623 prefixEnd_4199623 239602796297436409933199 := by
  unfold tailWord_4199623
  simp only [CollatzResearch.WordTrace]
  refine ⟨153172834464490584351235523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102115222976327056234157015 153172834464490584351235523)
  ·
    refine ⟨229759251696735876526853285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153172834464490584351235523 229759251696735876526853285)
    ·
      refine ⟨43079859693137976848784991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229759251696735876526853285 43079859693137976848784991)
      ·
        refine ⟨64619789539706965273177487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43079859693137976848784991 64619789539706965273177487)
        ·
          refine ⟨96929684309560447909766231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64619789539706965273177487 96929684309560447909766231)
          ·
            refine ⟨145394526464340671864649347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96929684309560447909766231 145394526464340671864649347)
            ·
              refine ⟨218091789696511007796974021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145394526464340671864649347 218091789696511007796974021)
              ·
                refine ⟨40892210568095813961932629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 218091789696511007796974021 40892210568095813961932629)
                ·
                  refine ⟨239602796297436409933199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40892210568095813961932629 239602796297436409933199)
                  ·
                    rfl

theorem cell23_4199623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 9].length) (baseStart_4199623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199623 prefixEnd_4199623 := by exact prefixLift 4199623
  have htrace : WordTrace (prefixWord ++ tailWord_4199623) baseStart_4199623 baseEnd_4199623 := by
    simpa [prefixWord, tailWord_4199623, baseEnd_4199623] using wordTrace_append hprefix tailTrace_4199623
  have hstable : (prefixWord ++ tailWord_4199623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199623).length < 2 ^ (prefixWord ++ tailWord_4199623).sum := by decide
  have hdescent : baseEnd_4199623 < baseStart_4199623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199633 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 9]
def baseStart_4199633 : Nat := 118140960795 + 4199633 * 2 ^ 59
def prefixEnd_4199633 : Nat := 4983230072969 + 3 ^ 40 * 4199633 * 2
def baseEnd_4199633 : Nat := 2156430301483472650273745

theorem tailTrace_4199633 : CollatzResearch.WordTrace tailWord_4199633 prefixEnd_4199633 2156430301483472650273745 := by
  unfold tailWord_4199633
  simp only [CollatzResearch.WordTrace]
  refine ⟨153173199194454356059099553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102115466129636237372733035 153173199194454356059099553)
  ·
    refine ⟨114879899395840767044324665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153173199194454356059099553 114879899395840767044324665)
    ·
      refine ⟨86159924546880575283243499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114879899395840767044324665 86159924546880575283243499)
      ·
        refine ⟨129239886820320862924865249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86159924546880575283243499 129239886820320862924865249)
        ·
          refine ⟨96929915115240647193648937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129239886820320862924865249 96929915115240647193648937)
          ·
            refine ⟨72697436336430485395236703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96929915115240647193648937 72697436336430485395236703)
            ·
              refine ⟨109046154504645728092855055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72697436336430485395236703 109046154504645728092855055)
              ·
                refine ⟨163569231756968592139282583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109046154504645728092855055 163569231756968592139282583)
                ·
                  refine ⟨245353847635452888208923875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163569231756968592139282583 245353847635452888208923875)
                  ·
                    refine ⟨368030771453179332313385813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 245353847635452888208923875 368030771453179332313385813)
                    ·
                      refine ⟨2156430301483472650273745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 368030771453179332313385813 2156430301483472650273745)
                      ·
                        rfl

theorem cell23_4199633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_4199633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199633 prefixEnd_4199633 := by exact prefixLift 4199633
  have htrace : WordTrace (prefixWord ++ tailWord_4199633) baseStart_4199633 baseEnd_4199633 := by
    simpa [prefixWord, tailWord_4199633, baseEnd_4199633] using wordTrace_append hprefix tailTrace_4199633
  have hstable : (prefixWord ++ tailWord_4199633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199633).length < 2 ^ (prefixWord ++ tailWord_4199633).sum := by decide
  have hdescent : baseEnd_4199633 < baseStart_4199633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199634 : List Nat := [3, 2, 2, 2, 1, 1, 1, 3, 4, 2, 2]
def baseStart_4199634 : Nat := 118140960795 + 4199634 * 2 ^ 59
def prefixEnd_4199634 : Nat := 4983230072969 + 3 ^ 40 * 4199634 * 2
def baseEnd_4199634 : Nat := 2156430814964127146361241

theorem tailTrace_4199634 : CollatzResearch.WordTrace tailWord_4199634 prefixEnd_4199634 2156430814964127146361241 := by
  unfold tailWord_4199634
  simp only [CollatzResearch.WordTrace]
  refine ⟨38293308916862683307471489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102115490444967155486590637 38293308916862683307471489)
  ·
    refine ⟨28719981687647012480603617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38293308916862683307471489 28719981687647012480603617)
    ·
      refine ⟨21539986265735259360452713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28719981687647012480603617 21539986265735259360452713)
      ·
        refine ⟨16154989699301444520339535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21539986265735259360452713 16154989699301444520339535)
        ·
          refine ⟨24232484548952166780509303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16154989699301444520339535 24232484548952166780509303)
          ·
            refine ⟨36348726823428250170763955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24232484548952166780509303 36348726823428250170763955)
            ·
              refine ⟨54523090235142375256145933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36348726823428250170763955 54523090235142375256145933)
              ·
                refine ⟨20446158838178390721054725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54523090235142375256145933 20446158838178390721054725)
                ·
                  refine ⟨3833654782158448260197761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20446158838178390721054725 3833654782158448260197761)
                  ·
                    refine ⟨2875241086618836195148321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3833654782158448260197761 2875241086618836195148321)
                    ·
                      refine ⟨2156430814964127146361241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2875241086618836195148321 2156430814964127146361241)
                      ·
                        rfl

theorem cell23_4199634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_4199634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199634 prefixEnd_4199634 := by exact prefixLift 4199634
  have htrace : WordTrace (prefixWord ++ tailWord_4199634) baseStart_4199634 baseEnd_4199634 := by
    simpa [prefixWord, tailWord_4199634, baseEnd_4199634] using wordTrace_append hprefix tailTrace_4199634
  have hstable : (prefixWord ++ tailWord_4199634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199634).length < 2 ^ (prefixWord ++ tailWord_4199634).sum := by decide
  have hdescent : baseEnd_4199634 < baseStart_4199634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199645 : List Nat := [1, 4, 3, 2, 3, 1, 2, 1, 2, 1, 3]
def baseStart_4199645 : Nat := 118140960795 + 4199645 * 2 ^ 59
def prefixEnd_4199645 : Nat := 4983230072969 + 3 ^ 40 * 4199645 * 2
def baseEnd_4199645 : Nat := 2156436463251326603323691

theorem tailTrace_4199645 : CollatzResearch.WordTrace tailWord_4199645 prefixEnd_4199645 2156436463251326603323691 := by
  unfold tailWord_4199645
  simp only [CollatzResearch.WordTrace]
  refine ⟨153173636870410882108536389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102115757913607254739024259 153173636870410882108536389)
  ·
    refine ⟨28720056913202040395350573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153173636870410882108536389 28720056913202040395350573)
    ·
      refine ⟨10770021342450765148256465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28720056913202040395350573 10770021342450765148256465)
      ·
        refine ⟨8077516006838073861192349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10770021342450765148256465 8077516006838073861192349)
        ·
          refine ⟨3029068502564277697947131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8077516006838073861192349 3029068502564277697947131)
          ·
            refine ⟨4543602753846416546920697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3029068502564277697947131 4543602753846416546920697)
            ·
              refine ⟨3407702065384812410190523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4543602753846416546920697 3407702065384812410190523)
              ·
                refine ⟨5111553098077218615285785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3407702065384812410190523 5111553098077218615285785)
                ·
                  refine ⟨3833664823557913961464339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5111553098077218615285785 3833664823557913961464339)
                  ·
                    refine ⟨5750497235336870942196509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3833664823557913961464339 5750497235336870942196509)
                    ·
                      refine ⟨2156436463251326603323691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5750497235336870942196509 2156436463251326603323691)
                      ·
                        rfl

theorem cell23_4199645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_4199645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199645 prefixEnd_4199645 := by exact prefixLift 4199645
  have htrace : WordTrace (prefixWord ++ tailWord_4199645) baseStart_4199645 baseEnd_4199645 := by
    simpa [prefixWord, tailWord_4199645, baseEnd_4199645] using wordTrace_append hprefix tailTrace_4199645
  have hstable : (prefixWord ++ tailWord_4199645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199645).length < 2 ^ (prefixWord ++ tailWord_4199645).sum := by decide
  have hdescent : baseEnd_4199645 < baseStart_4199645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199690 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4]
def baseStart_4199690 : Nat := 118140960795 + 4199690 * 2 ^ 59
def prefixEnd_4199690 : Nat := 4983230072969 + 3 ^ 40 * 4199690 * 2
def baseEnd_4199690 : Nat := 2156459569880778927260983

theorem tailTrace_4199690 : CollatzResearch.WordTrace tailWord_4199690 prefixEnd_4199690 2156459569880778927260983 := by
  unfold tailWord_4199690
  simp only [CollatzResearch.WordTrace]
  refine ⟨38293819538811963698481131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102116852103498569862616349 38293819538811963698481131)
  ·
    refine ⟨57440729308217945547721697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38293819538811963698481131 57440729308217945547721697)
    ·
      refine ⟨43080546981163459160791273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57440729308217945547721697 43080546981163459160791273)
      ·
        refine ⟨32310410235872594370593455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43080546981163459160791273 32310410235872594370593455)
        ·
          refine ⟨48465615353808891555890183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32310410235872594370593455 48465615353808891555890183)
          ·
            refine ⟨72698423030713337333835275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48465615353808891555890183 72698423030713337333835275)
            ·
              refine ⟨109047634546070006000752913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72698423030713337333835275 109047634546070006000752913)
              ·
                refine ⟨81785725909552504500564685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109047634546070006000752913 81785725909552504500564685)
                ·
                  refine ⟨30669647216082189187711757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81785725909552504500564685 30669647216082189187711757)
                  ·
                    refine ⟨11501117706030820945391909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30669647216082189187711757 11501117706030820945391909)
                    ·
                      refine ⟨2156459569880778927260983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11501117706030820945391909 2156459569880778927260983)
                      ·
                        rfl

theorem cell23_4199690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_4199690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199690 prefixEnd_4199690 := by exact prefixLift 4199690
  have htrace : WordTrace (prefixWord ++ tailWord_4199690) baseStart_4199690 baseEnd_4199690 := by
    simpa [prefixWord, tailWord_4199690, baseEnd_4199690] using wordTrace_append hprefix tailTrace_4199690
  have hstable : (prefixWord ++ tailWord_4199690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199690).length < 2 ^ (prefixWord ++ tailWord_4199690).sum := by decide
  have hdescent : baseEnd_4199690 < baseStart_4199690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199717 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 5, 4]
def baseStart_4199717 : Nat := 118140960795 + 4199717 * 2 ^ 59
def prefixEnd_4199717 : Nat := 4983230072969 + 3 ^ 40 * 4199717 * 2
def baseEnd_4199717 : Nat := 718824477952816773874453

theorem tailTrace_4199717 : CollatzResearch.WordTrace tailWord_4199717 prefixEnd_4199717 718824477952816773874453 := by
  unfold tailWord_4199717
  simp only [CollatzResearch.WordTrace]
  refine ⟨153176262926150038405157405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102117508617433358936771603 153176262926150038405157405)
  ·
    refine ⟨57441098597306264401934027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153176262926150038405157405 57441098597306264401934027)
    ·
      refine ⟨86161647895959396602901041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57441098597306264401934027 86161647895959396602901041)
      ·
        refine ⟨64621235921969547452175781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86161647895959396602901041 64621235921969547452175781)
        ·
          refine ⟨12116481735369290147282959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64621235921969547452175781 12116481735369290147282959)
          ·
            refine ⟨18174722603053935220924439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12116481735369290147282959 18174722603053935220924439)
            ·
              refine ⟨27262083904580902831386659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18174722603053935220924439 27262083904580902831386659)
              ·
                refine ⟨40893125856871354247079989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27262083904580902831386659 40893125856871354247079989)
                ·
                  refine ⟨3833730549081689460663749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40893125856871354247079989 3833730549081689460663749)
                  ·
                    refine ⟨718824477952816773874453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3833730549081689460663749 718824477952816773874453)
                    ·
                      rfl

theorem cell23_4199717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5, 4].length) (baseStart_4199717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199717 prefixEnd_4199717 := by exact prefixLift 4199717
  have htrace : WordTrace (prefixWord ++ tailWord_4199717) baseStart_4199717 baseEnd_4199717 := by
    simpa [prefixWord, tailWord_4199717, baseEnd_4199717] using wordTrace_append hprefix tailTrace_4199717
  have hstable : (prefixWord ++ tailWord_4199717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199717).length < 2 ^ (prefixWord ++ tailWord_4199717).sum := by decide
  have hdescent : baseEnd_4199717 < baseStart_4199717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199764 : List Nat := [2, 4, 1, 1, 2, 1, 5, 1, 6]
def baseStart_4199764 : Nat := 118140960795 + 4199764 * 2 ^ 59
def prefixEnd_4199764 : Nat := 4983230072969 + 3 ^ 40 * 4199764 * 2
def baseEnd_4199764 : Nat := 239610840827690181970627

theorem tailTrace_4199764 : CollatzResearch.WordTrace tailWord_4199764 prefixEnd_4199764 239610840827690181970627 := by
  unfold tailWord_4199764
  simp only [CollatzResearch.WordTrace]
  refine ⟨76588988578489882716059173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102118651437986510288078897 76588988578489882716059173)
  ·
    refine ⟨14360435358466853009261095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76588988578489882716059173 14360435358466853009261095)
    ·
      refine ⟨21540653037700279513891643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14360435358466853009261095 21540653037700279513891643)
      ·
        refine ⟨32310979556550419270837465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21540653037700279513891643 32310979556550419270837465)
        ·
          refine ⟨24233234667412814453128099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32310979556550419270837465 24233234667412814453128099)
          ·
            refine ⟨36349852001119221679692149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24233234667412814453128099 36349852001119221679692149)
            ·
              refine ⟨3407798625104927032471139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36349852001119221679692149 3407798625104927032471139)
              ·
                refine ⟨5111697937657390548706709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3407798625104927032471139 5111697937657390548706709)
                ·
                  refine ⟨239610840827690181970627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5111697937657390548706709 239610840827690181970627)
                  ·
                    rfl

theorem cell23_4199764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_4199764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199764 prefixEnd_4199764 := by exact prefixLift 4199764
  have htrace : WordTrace (prefixWord ++ tailWord_4199764) baseStart_4199764 baseEnd_4199764 := by
    simpa [prefixWord, tailWord_4199764, baseEnd_4199764] using wordTrace_append hprefix tailTrace_4199764
  have hstable : (prefixWord ++ tailWord_4199764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199764).length < 2 ^ (prefixWord ++ tailWord_4199764).sum := by decide
  have hdescent : baseEnd_4199764 < baseStart_4199764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199770 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7]
def baseStart_4199770 : Nat := 118140960795 + 4199770 * 2 ^ 59
def prefixEnd_4199770 : Nat := 4983230072969 + 3 ^ 40 * 4199770 * 2
def baseEnd_4199770 : Nat := 2156500648333138614260615

theorem tailTrace_4199770 : CollatzResearch.WordTrace tailWord_4199770 prefixEnd_4199770 2156500648333138614260615 := by
  unfold tailWord_4199770
  simp only [CollatzResearch.WordTrace]
  refine ⟨38294548998739507114209191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102118797329972018971224509 38294548998739507114209191)
  ·
    refine ⟨57441823498109260671313787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38294548998739507114209191 57441823498109260671313787)
    ·
      refine ⟨86162735247163891006970681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57441823498109260671313787 86162735247163891006970681)
      ·
        refine ⟨64622051435372918255228011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86162735247163891006970681 64622051435372918255228011)
        ·
          refine ⟨96933077153059377382842017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64622051435372918255228011 96933077153059377382842017)
          ·
            refine ⟨72699807864794533037131513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96933077153059377382842017 72699807864794533037131513)
            ·
              refine ⟨54524855898595899777848635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72699807864794533037131513 54524855898595899777848635)
              ·
                refine ⟨81787283847893849666772953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54524855898595899777848635 81787283847893849666772953)
                ·
                  refine ⟨61340462885920387250079715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81787283847893849666772953 61340462885920387250079715)
                  ·
                    refine ⟨92010694328880580875119573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61340462885920387250079715 92010694328880580875119573)
                    ·
                      refine ⟨2156500648333138614260615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92010694328880580875119573 2156500648333138614260615)
                      ·
                        rfl

theorem cell23_4199770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_4199770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199770 prefixEnd_4199770 := by exact prefixLift 4199770
  have htrace : WordTrace (prefixWord ++ tailWord_4199770) baseStart_4199770 baseEnd_4199770 := by
    simpa [prefixWord, tailWord_4199770, baseEnd_4199770] using wordTrace_append hprefix tailTrace_4199770
  have hstable : (prefixWord ++ tailWord_4199770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199770).length < 2 ^ (prefixWord ++ tailWord_4199770).sum := by decide
  have hdescent : baseEnd_4199770 < baseStart_4199770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199834 : List Nat := [3, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3]
def baseStart_4199834 : Nat := 118140960795 + 4199834 * 2 ^ 59
def prefixEnd_4199834 : Nat := 4983230072969 + 3 ^ 40 * 4199834 * 2
def baseEnd_4199834 : Nat := 2156533511095026363860321

theorem tailTrace_4199834 : CollatzResearch.WordTrace tailWord_4199834 prefixEnd_4199834 2156533511095026363860321 := by
  unfold tailWord_4199834
  simp only [CollatzResearch.WordTrace]
  refine ⟨38295132566681541846791639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102120353511150778258111037 38295132566681541846791639)
  ·
    refine ⟨57442698850022312770187459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38295132566681541846791639 57442698850022312770187459)
    ·
      refine ⟨86164048275033469155281189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57442698850022312770187459 86164048275033469155281189)
      ·
        refine ⟨16155759051568775466615223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86164048275033469155281189 16155759051568775466615223)
        ·
          refine ⟨24233638577353163199922835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16155759051568775466615223 24233638577353163199922835)
          ·
            refine ⟨36350457866029744799884253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24233638577353163199922835 36350457866029744799884253)
            ·
              refine ⟨13631421699761154299956595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36350457866029744799884253 13631421699761154299956595)
              ·
                refine ⟨20447132549641731449934893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13631421699761154299956595 20447132549641731449934893)
                ·
                  refine ⟨7667674706115649293725585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20447132549641731449934893 7667674706115649293725585)
                  ·
                    refine ⟨5750756029586736970294189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7667674706115649293725585 5750756029586736970294189)
                    ·
                      refine ⟨2156533511095026363860321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5750756029586736970294189 2156533511095026363860321)
                      ·
                        rfl

theorem cell23_4199834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_4199834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199834 prefixEnd_4199834 := by exact prefixLift 4199834
  have htrace : WordTrace (prefixWord ++ tailWord_4199834) baseStart_4199834 baseEnd_4199834 := by
    simpa [prefixWord, tailWord_4199834, baseEnd_4199834] using wordTrace_append hprefix tailTrace_4199834
  have hstable : (prefixWord ++ tailWord_4199834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199834).length < 2 ^ (prefixWord ++ tailWord_4199834).sum := by decide
  have hdescent : baseEnd_4199834 < baseStart_4199834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199837 : List Nat := [1, 4, 2, 1, 3, 1, 2, 9]
def baseStart_4199837 : Nat := 118140960795 + 4199837 * 2 ^ 59
def prefixEnd_4199837 : Nat := 4983230072969 + 3 ^ 40 * 4199837 * 2
def baseEnd_4199837 : Nat := 79871668575444068597141

theorem tailTrace_4199837 : CollatzResearch.WordTrace tailWord_4199837 prefixEnd_4199837 79871668575444068597141 := by
  unfold tailWord_4199837
  simp only [CollatzResearch.WordTrace]
  refine ⟨153180639685715298899525765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102120426457143532599683843 153180639685715298899525765)
  ·
    refine ⟨28721369941071618543661081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153180639685715298899525765 28721369941071618543661081)
    ·
      refine ⟨21541027455803713907745811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28721369941071618543661081 21541027455803713907745811)
      ·
        refine ⟨32311541183705570861618717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21541027455803713907745811 32311541183705570861618717)
        ·
          refine ⟨12116827943889589073107019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32311541183705570861618717 12116827943889589073107019)
          ·
            refine ⟨18175241915834383609660529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12116827943889589073107019 18175241915834383609660529)
            ·
              refine ⟨13631431436875787707245397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18175241915834383609660529 13631431436875787707245397)
              ·
                refine ⟨79871668575444068597141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13631431436875787707245397 79871668575444068597141)
                ·
                  rfl

theorem cell23_4199837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 9].length) (baseStart_4199837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199837 prefixEnd_4199837 := by exact prefixLift 4199837
  have htrace : WordTrace (prefixWord ++ tailWord_4199837) baseStart_4199837 baseEnd_4199837 := by
    simpa [prefixWord, tailWord_4199837, baseEnd_4199837] using wordTrace_append hprefix tailTrace_4199837
  have hstable : (prefixWord ++ tailWord_4199837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199837).length < 2 ^ (prefixWord ++ tailWord_4199837).sum := by decide
  have hdescent : baseEnd_4199837 < baseStart_4199837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199864 : List Nat := [2, 1, 2, 1, 2, 2, 2, 3, 4, 1, 3]
def baseStart_4199864 : Nat := 118140960795 + 4199864 * 2 ^ 59
def prefixEnd_4199864 : Nat := 4983230072969 + 3 ^ 40 * 4199864 * 2
def baseEnd_4199864 : Nat := 2156548915514661246485183

theorem tailTrace_4199864 : CollatzResearch.WordTrace tailWord_4199864 prefixEnd_4199864 2156548915514661246485183 := by
  unfold tailWord_4199864
  simp only [CollatzResearch.WordTrace]
  refine ⟨76590812228308741255379323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102121082971078321673839097 76590812228308741255379323)
  ·
    refine ⟨114886218342463111883068985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76590812228308741255379323 114886218342463111883068985)
    ·
      refine ⟨86164663756847333912301739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114886218342463111883068985 86164663756847333912301739)
      ·
        refine ⟨129246995635271000868452609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86164663756847333912301739 129246995635271000868452609)
        ·
          refine ⟨96935246726453250651339457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129246995635271000868452609 96935246726453250651339457)
          ·
            refine ⟨72701435044839937988504593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96935246726453250651339457 72701435044839937988504593)
            ·
              refine ⟨54526076283629953491378445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72701435044839937988504593 54526076283629953491378445)
              ·
                refine ⟨20447278606361232559266917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54526076283629953491378445 20447278606361232559266917)
                ·
                  refine ⟨3833864738692731104862547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20447278606361232559266917 3833864738692731104862547)
                  ·
                    refine ⟨5750797108039096657293821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3833864738692731104862547 5750797108039096657293821)
                    ·
                      refine ⟨2156548915514661246485183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5750797108039096657293821 2156548915514661246485183)
                      ·
                        rfl

theorem cell23_4199864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 4, 1, 3].length) (baseStart_4199864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199864 prefixEnd_4199864 := by exact prefixLift 4199864
  have htrace : WordTrace (prefixWord ++ tailWord_4199864) baseStart_4199864 baseEnd_4199864 := by
    simpa [prefixWord, tailWord_4199864, baseEnd_4199864] using wordTrace_append hprefix tailTrace_4199864
  have hstable : (prefixWord ++ tailWord_4199864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199864).length < 2 ^ (prefixWord ++ tailWord_4199864).sum := by decide
  have hdescent : baseEnd_4199864 < baseStart_4199864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199865 : List Nat := [1, 2, 1, 4, 4, 1, 1, 4, 1, 2, 2]
def baseStart_4199865 : Nat := 118140960795 + 4199865 * 2 ^ 59
def prefixEnd_4199865 : Nat := 4983230072969 + 3 ^ 40 * 4199865 * 2
def baseEnd_4199865 : Nat := 2156549428995315742572679

theorem tailTrace_4199865 : CollatzResearch.WordTrace tailWord_4199865 prefixEnd_4199865 2156549428995315742572679 := by
  unfold tailWord_4199865
  simp only [CollatzResearch.WordTrace]
  refine ⟨153181660929613859681545049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102121107286409239787696699 153181660929613859681545049)
  ·
    refine ⟨114886245697210394761158787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153181660929613859681545049 114886245697210394761158787)
    ·
      refine ⟨172329368545815592141738181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114886245697210394761158787 172329368545815592141738181)
      ·
        refine ⟨32311756602340423526575909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172329368545815592141738181 32311756602340423526575909)
        ·
          refine ⟨6058454362938829411232983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32311756602340423526575909 6058454362938829411232983)
          ·
            refine ⟨9087681544408244116849475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6058454362938829411232983 9087681544408244116849475)
            ·
              refine ⟨13631522316612366175274213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9087681544408244116849475 13631522316612366175274213)
              ·
                refine ⟨2555910434364818657863915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13631522316612366175274213 2555910434364818657863915)
                ·
                  refine ⟨3833865651547227986795873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2555910434364818657863915 3833865651547227986795873)
                  ·
                    refine ⟨2875399238660420990096905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3833865651547227986795873 2875399238660420990096905)
                    ·
                      refine ⟨2156549428995315742572679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2875399238660420990096905 2156549428995315742572679)
                      ·
                        rfl

theorem cell23_4199865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_4199865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199865 prefixEnd_4199865 := by exact prefixLift 4199865
  have htrace : WordTrace (prefixWord ++ tailWord_4199865) baseStart_4199865 baseEnd_4199865 := by
    simpa [prefixWord, tailWord_4199865, baseEnd_4199865] using wordTrace_append hprefix tailTrace_4199865
  have hstable : (prefixWord ++ tailWord_4199865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199865).length < 2 ^ (prefixWord ++ tailWord_4199865).sum := by decide
  have hdescent : baseEnd_4199865 < baseStart_4199865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199904 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 3, 4, 2]
def baseStart_4199904 : Nat := 118140960795 + 4199904 * 2 ^ 59
def prefixEnd_4199904 : Nat := 4983230072969 + 3 ^ 40 * 4199904 * 2
def baseEnd_4199904 : Nat := 2156569454740841089984999

theorem tailTrace_4199904 : CollatzResearch.WordTrace tailWord_4199904 prefixEnd_4199904 2156569454740841089984999 := by
  unfold tailWord_4199904
  simp only [CollatzResearch.WordTrace]
  refine ⟨76591541688236284671107383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102122055584315046228143177 76591541688236284671107383)
  ·
    refine ⟨114887312532354427006661075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76591541688236284671107383 114887312532354427006661075)
    ·
      refine ⟨172330968798531640509991613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114887312532354427006661075 172330968798531640509991613)
      ·
        refine ⟨64624113299449365191246855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172330968798531640509991613 64624113299449365191246855)
        ·
          refine ⟨96936169949174047786870283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64624113299449365191246855 96936169949174047786870283)
          ·
            refine ⟨145404254923761071680305425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96936169949174047786870283 145404254923761071680305425)
            ·
              refine ⟨109053191192820803760229069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145404254923761071680305425 109053191192820803760229069)
              ·
                refine ⟨40894946697307801410085901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109053191192820803760229069 40894946697307801410085901)
                ·
                  refine ⟨15335605011490425528782213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40894946697307801410085901 15335605011490425528782213)
                  ·
                    refine ⟨2875425939654454786646665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15335605011490425528782213 2875425939654454786646665)
                    ·
                      refine ⟨2156569454740841089984999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2875425939654454786646665 2156569454740841089984999)
                      ·
                        rfl

theorem cell23_4199904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 3, 4, 2].length) (baseStart_4199904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199904 prefixEnd_4199904 := by exact prefixLift 4199904
  have htrace : WordTrace (prefixWord ++ tailWord_4199904) baseStart_4199904 baseEnd_4199904 := by
    simpa [prefixWord, tailWord_4199904, baseEnd_4199904] using wordTrace_append hprefix tailTrace_4199904
  have hstable : (prefixWord ++ tailWord_4199904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199904).length < 2 ^ (prefixWord ++ tailWord_4199904).sum := by decide
  have hdescent : baseEnd_4199904 < baseStart_4199904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199977 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 1, 9, 4]
def baseStart_4199977 : Nat := 118140960795 + 4199977 * 2 ^ 59
def prefixEnd_4199977 : Nat := 4983230072969 + 3 ^ 40 * 4199977 * 2
def baseEnd_4199977 : Nat := 2156606938828619304372163

theorem tailTrace_4199977 : CollatzResearch.WordTrace tailWord_4199977 prefixEnd_4199977 2156606938828619304372163 := by
  unfold tailWord_4199977
  simp only [CollatzResearch.WordTrace]
  refine ⟨153185745905208102809622185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102123830603472068539748123 153185745905208102809622185)
  ·
    refine ⟨114889309428906077107216639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153185745905208102809622185 114889309428906077107216639)
    ·
      refine ⟨172333964143359115660824959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114889309428906077107216639 172333964143359115660824959)
      ·
        refine ⟨258500946215038673491237439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172333964143359115660824959 258500946215038673491237439)
        ·
          refine ⟨387751419322558010236856159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258500946215038673491237439 387751419322558010236856159)
          ·
            refine ⟨581627128983837015355284239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387751419322558010236856159 581627128983837015355284239)
            ·
              refine ⟨872440693475755523032926359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581627128983837015355284239 872440693475755523032926359)
              ·
                refine ⟨1308661040213633284549389539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 872440693475755523032926359 1308661040213633284549389539)
                ·
                  refine ⟨1962991560320449926824084309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1308661040213633284549389539 1962991560320449926824084309)
                  ·
                    refine ⟨11501903673752636289984869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1962991560320449926824084309 11501903673752636289984869)
                    ·
                      refine ⟨2156606938828619304372163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11501903673752636289984869 2156606938828619304372163)
                      ·
                        rfl

theorem cell23_4199977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 9, 4].length) (baseStart_4199977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199977 prefixEnd_4199977 := by exact prefixLift 4199977
  have htrace : WordTrace (prefixWord ++ tailWord_4199977) baseStart_4199977 baseEnd_4199977 := by
    simpa [prefixWord, tailWord_4199977, baseEnd_4199977] using wordTrace_append hprefix tailTrace_4199977
  have hstable : (prefixWord ++ tailWord_4199977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199977).length < 2 ^ (prefixWord ++ tailWord_4199977).sum := by decide
  have hdescent : baseEnd_4199977 < baseStart_4199977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199978 : List Nat := [3, 1, 4, 1, 1, 1, 5, 2, 5]
def baseStart_4199978 : Nat := 118140960795 + 4199978 * 2 ^ 59
def prefixEnd_4199978 : Nat := 4983230072969 + 3 ^ 40 * 4199978 * 2
def baseEnd_4199978 : Nat := 239623050256585977828851

theorem tailTrace_4199978 : CollatzResearch.WordTrace tailWord_4199978 prefixEnd_4199978 239623050256585977828851 := by
  unfold tailWord_4199978
  simp only [CollatzResearch.WordTrace]
  refine ⟨38296445594551119995102147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102123854918802986653605725 38296445594551119995102147)
  ·
    refine ⟨57444668391826679992653221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38296445594551119995102147 57444668391826679992653221)
    ·
      refine ⟨10770875323467502498622479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57444668391826679992653221 10770875323467502498622479)
      ·
        refine ⟨16156312985201253747933719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10770875323467502498622479 16156312985201253747933719)
        ·
          refine ⟨24234469477801880621900579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16156312985201253747933719 24234469477801880621900579)
          ·
            refine ⟨36351704216702820932850869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24234469477801880621900579 36351704216702820932850869)
            ·
              refine ⟨3407972270315889462454769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36351704216702820932850869 3407972270315889462454769)
              ·
                refine ⟨2555979202736917096841077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3407972270315889462454769 2555979202736917096841077)
                ·
                  refine ⟨239623050256585977828851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2555979202736917096841077 239623050256585977828851)
                  ·
                    rfl

theorem cell23_4199978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2, 5].length) (baseStart_4199978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199978 prefixEnd_4199978 := by exact prefixLift 4199978
  have htrace : WordTrace (prefixWord ++ tailWord_4199978) baseStart_4199978 baseEnd_4199978 := by
    simpa [prefixWord, tailWord_4199978, baseEnd_4199978] using wordTrace_append hprefix tailTrace_4199978
  have hstable : (prefixWord ++ tailWord_4199978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199978).length < 2 ^ (prefixWord ++ tailWord_4199978).sum := by decide
  have hdescent : baseEnd_4199978 < baseStart_4199978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4199994 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4]
def baseStart_4199994 : Nat := 118140960795 + 4199994 * 2 ^ 59
def prefixEnd_4199994 : Nat := 4983230072969 + 3 ^ 40 * 4199994 * 2
def baseEnd_4199994 : Nat := 2156615667999745737859585

theorem tailTrace_4199994 : CollatzResearch.WordTrace tailWord_4199994 prefixEnd_4199994 2156615667999745737859585 := by
  unfold tailWord_4199994
  simp only [CollatzResearch.WordTrace]
  refine ⟨38296591486536628678247759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102124243964097676475327357 38296591486536628678247759)
  ·
    refine ⟨57444887229804943017371639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38296591486536628678247759 57444887229804943017371639)
    ·
      refine ⟨86167330844707414526057459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57444887229804943017371639 86167330844707414526057459)
      ·
        refine ⟨129250996267061121789086189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86167330844707414526057459 129250996267061121789086189)
        ·
          refine ⟨48469123600147920670907321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129250996267061121789086189 48469123600147920670907321)
          ·
            refine ⟨36351842700110940503180491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48469123600147920670907321 36351842700110940503180491)
            ·
              refine ⟨54527764050166410754770737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36351842700110940503180491 54527764050166410754770737)
              ·
                refine ⟨40895823037624808066078053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54527764050166410754770737 40895823037624808066078053)
                ·
                  refine ⟨7667966819554651512389635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40895823037624808066078053 7667966819554651512389635)
                  ·
                    refine ⟨11501950229331977268584453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7667966819554651512389635 11501950229331977268584453)
                    ·
                      refine ⟨2156615667999745737859585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11501950229331977268584453 2156615667999745737859585)
                      ·
                        rfl

theorem cell23_4199994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_4199994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4199994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4199994 prefixEnd_4199994 := by exact prefixLift 4199994
  have htrace : WordTrace (prefixWord ++ tailWord_4199994) baseStart_4199994 baseEnd_4199994 := by
    simpa [prefixWord, tailWord_4199994, baseEnd_4199994] using wordTrace_append hprefix tailTrace_4199994
  have hstable : (prefixWord ++ tailWord_4199994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4199994).length < 2 ^ (prefixWord ++ tailWord_4199994).sum := by decide
  have hdescent : baseEnd_4199994 < baseStart_4199994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4199994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200029 : List Nat := [1, 4, 4, 2, 2, 1, 2, 2, 5]
def baseStart_4200029 : Nat := 118140960795 + 4200029 * 2 ^ 59
def prefixEnd_4200029 : Nat := 4983230072969 + 3 ^ 40 * 4200029 * 2
def baseEnd_4200029 : Nat := 239625959980294788991325

theorem tailTrace_4200029 : CollatzResearch.WordTrace tailWord_4200029 prefixEnd_4200029 239625959980294788991325 := by
  unfold tailWord_4200029
  simp only [CollatzResearch.WordTrace]
  refine ⟨153187642501019715690515141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102125095000679810460343427 153187642501019715690515141)
  ·
    refine ⟨28722682968941196691971589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153187642501019715690515141 28722682968941196691971589)
    ·
      refine ⟨5385503056676474379744673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28722682968941196691971589 5385503056676474379744673)
      ·
        refine ⟨4039127292507355784808505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5385503056676474379744673 4039127292507355784808505)
        ·
          refine ⟨3029345469380516838606379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4039127292507355784808505 3029345469380516838606379)
          ·
            refine ⟨4544018204070775257909569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3029345469380516838606379 4544018204070775257909569)
            ·
              refine ⟨3408013653053081443432177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4544018204070775257909569 3408013653053081443432177)
              ·
                refine ⟨2556010239789811082574133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3408013653053081443432177 2556010239789811082574133)
                ·
                  refine ⟨239625959980294788991325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2556010239789811082574133 239625959980294788991325)
                  ·
                    rfl

theorem cell23_4200029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2, 5].length) (baseStart_4200029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200029 prefixEnd_4200029 := by exact prefixLift 4200029
  have htrace : WordTrace (prefixWord ++ tailWord_4200029) baseStart_4200029 baseEnd_4200029 := by
    simpa [prefixWord, tailWord_4200029, baseEnd_4200029] using wordTrace_append hprefix tailTrace_4200029
  have hstable : (prefixWord ++ tailWord_4200029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200029).length < 2 ^ (prefixWord ++ tailWord_4200029).sum := by decide
  have hdescent : baseEnd_4200029 < baseStart_4200029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200044 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 3]
def baseStart_4200044 : Nat := 118140960795 + 4200044 * 2 ^ 59
def prefixEnd_4200044 : Nat := 4983230072969 + 3 ^ 40 * 4200044 * 2
def baseEnd_4200044 : Nat := 2156641342032470542234355

theorem tailTrace_4200044 : CollatzResearch.WordTrace tailWord_4200044 prefixEnd_4200044 2156641342032470542234355 := by
  unfold tailWord_4200044
  simp only [CollatzResearch.WordTrace]
  refine ⟨76594094797982686626155593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102125459730643582168207457 76594094797982686626155593)
  ·
    refine ⟨57445571098487014969616695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76594094797982686626155593 57445571098487014969616695)
    ·
      refine ⟨86168356647730522454425043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57445571098487014969616695 86168356647730522454425043)
      ·
        refine ⟨129252534971595783681637565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86168356647730522454425043 129252534971595783681637565)
        ·
          refine ⟨48469700614348418880614087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129252534971595783681637565 48469700614348418880614087)
          ·
            refine ⟨72704550921522628320921131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48469700614348418880614087 72704550921522628320921131)
            ·
              refine ⟨109056826382283942481381697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72704550921522628320921131 109056826382283942481381697)
              ·
                refine ⟨81792619786712956861036273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109056826382283942481381697 81792619786712956861036273)
                ·
                  refine ⟨61344464840034717645777205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81792619786712956861036273 61344464840034717645777205)
                  ·
                    refine ⟨5751043578753254779291613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61344464840034717645777205 5751043578753254779291613)
                    ·
                      refine ⟨2156641342032470542234355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5751043578753254779291613 2156641342032470542234355)
                      ·
                        rfl

theorem cell23_4200044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 3].length) (baseStart_4200044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200044 prefixEnd_4200044 := by exact prefixLift 4200044
  have htrace : WordTrace (prefixWord ++ tailWord_4200044) baseStart_4200044 baseEnd_4200044 := by
    simpa [prefixWord, tailWord_4200044, baseEnd_4200044] using wordTrace_append hprefix tailTrace_4200044
  have hstable : (prefixWord ++ tailWord_4200044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200044).length < 2 ^ (prefixWord ++ tailWord_4200044).sum := by decide
  have hdescent : baseEnd_4200044 < baseStart_4200044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200064 : List Nat := [2, 1, 1, 2, 1, 4, 1, 3, 3, 5]
def baseStart_4200064 : Nat := 118140960795 + 4200064 * 2 ^ 59
def prefixEnd_4200064 : Nat := 4983230072969 + 3 ^ 40 * 4200064 * 2
def baseEnd_4200064 : Nat := 718883870548520154661421

theorem tailTrace_4200064 : CollatzResearch.WordTrace tailWord_4200064 prefixEnd_4200064 718883870548520154661421 := by
  unfold tailWord_4200064
  simp only [CollatzResearch.WordTrace]
  refine ⟨76594459527946458334019623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102125946037261944445359497 76594459527946458334019623)
  ·
    refine ⟨114891689291919687501029435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76594459527946458334019623 114891689291919687501029435)
    ·
      refine ⟨172337533937879531251544153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114891689291919687501029435 172337533937879531251544153)
      ·
        refine ⟨129253150453409648438658115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172337533937879531251544153 129253150453409648438658115)
        ·
          refine ⟨193879725680114472657987173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129253150453409648438658115 193879725680114472657987173)
          ·
            refine ⟨36352448565021463623372595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193879725680114472657987173 36352448565021463623372595)
            ·
              refine ⟨54528672847532195435058893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36352448565021463623372595 54528672847532195435058893)
              ·
                refine ⟨20448252317824573288147085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54528672847532195435058893 20448252317824573288147085)
                ·
                  refine ⟨7668094619184214983055157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20448252317824573288147085 7668094619184214983055157)
                  ·
                    refine ⟨718883870548520154661421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7668094619184214983055157 718883870548520154661421)
                    ·
                      rfl

theorem cell23_4200064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 3, 5].length) (baseStart_4200064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200064 prefixEnd_4200064 := by exact prefixLift 4200064
  have htrace : WordTrace (prefixWord ++ tailWord_4200064) baseStart_4200064 baseEnd_4200064 := by
    simpa [prefixWord, tailWord_4200064, baseEnd_4200064] using wordTrace_append hprefix tailTrace_4200064
  have hstable : (prefixWord ++ tailWord_4200064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200064).length < 2 ^ (prefixWord ++ tailWord_4200064).sum := by decide
  have hdescent : baseEnd_4200064 < baseStart_4200064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200072 : List Nat := [2, 1, 3, 5, 1, 1, 2, 3, 1, 4]
def baseStart_4200072 : Nat := 118140960795 + 4200072 * 2 ^ 59
def prefixEnd_4200072 : Nat := 4983230072969 + 3 ^ 40 * 4200072 * 2
def baseEnd_4200072 : Nat := 718885239830265477561409

theorem tailTrace_4200072 : CollatzResearch.WordTrace tailWord_4200072 prefixEnd_4200072 718885239830265477561409 := by
  unfold tailWord_4200072
  simp only [CollatzResearch.WordTrace]
  refine ⟨76594605419931967017165235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102126140559909289356220313 76594605419931967017165235)
  ·
    refine ⟨114891908129897950525747853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76594605419931967017165235 114891908129897950525747853)
    ·
      refine ⟨43084465548711731447155445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114891908129897950525747853 43084465548711731447155445)
      ·
        refine ⟨4039168645191724823170823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43084465548711731447155445 4039168645191724823170823)
        ·
          refine ⟨6058752967787587234756235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4039168645191724823170823 6058752967787587234756235)
          ·
            refine ⟨9088129451681380852134353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6058752967787587234756235 9088129451681380852134353)
            ·
              refine ⟨6816097088761035639100765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9088129451681380852134353 6816097088761035639100765)
              ·
                refine ⟨2556036408285388364662787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6816097088761035639100765 2556036408285388364662787)
                ·
                  refine ⟨3834054612428082546994181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2556036408285388364662787 3834054612428082546994181)
                  ·
                    refine ⟨718885239830265477561409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3834054612428082546994181 718885239830265477561409)
                    ·
                      rfl

theorem cell23_4200072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_4200072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200072 prefixEnd_4200072 := by exact prefixLift 4200072
  have htrace : WordTrace (prefixWord ++ tailWord_4200072) baseStart_4200072 baseEnd_4200072 := by
    simpa [prefixWord, tailWord_4200072, baseEnd_4200072] using wordTrace_append hprefix tailTrace_4200072
  have hstable : (prefixWord ++ tailWord_4200072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200072).length < 2 ^ (prefixWord ++ tailWord_4200072).sum := by decide
  have hdescent : baseEnd_4200072 < baseStart_4200072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200121 : List Nat := [1, 2, 1, 4, 1, 1, 2, 3, 3, 2, 3]
def baseStart_4200121 : Nat := 118140960795 + 4200121 * 2 ^ 59
def prefixEnd_4200121 : Nat := 4983230072969 + 3 ^ 40 * 4200121 * 2
def baseEnd_4200121 : Nat := 2156680880042866740971501

theorem tailTrace_4200121 : CollatzResearch.WordTrace tailWord_4200121 prefixEnd_4200121 2156680880042866740971501 := by
  unfold tailWord_4200121
  simp only [CollatzResearch.WordTrace]
  refine ⟨153190998016686415402864217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102127332011124276935242811 153190998016686415402864217)
  ·
    refine ⟨114893248512514811552148163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153190998016686415402864217 114893248512514811552148163)
    ·
      refine ⟨172339872768772217328222245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114893248512514811552148163 172339872768772217328222245)
      ·
        refine ⟨32313726144144790749041671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172339872768772217328222245 32313726144144790749041671)
        ·
          refine ⟨48470589216217186123562507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32313726144144790749041671 48470589216217186123562507)
          ·
            refine ⟨72705883824325779185343761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48470589216217186123562507 72705883824325779185343761)
            ·
              refine ⟨54529412868244334389007821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72705883824325779185343761 54529412868244334389007821)
              ·
                refine ⟨20448529825591625395877933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54529412868244334389007821 20448529825591625395877933)
                ·
                  refine ⟨7668198684596859523454225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20448529825591625395877933 7668198684596859523454225)
                  ·
                    refine ⟨5751149013447644642590669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7668198684596859523454225 5751149013447644642590669)
                    ·
                      refine ⟨2156680880042866740971501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5751149013447644642590669 2156680880042866740971501)
                      ·
                        rfl

theorem cell23_4200121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_4200121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200121 prefixEnd_4200121 := by exact prefixLift 4200121
  have htrace : WordTrace (prefixWord ++ tailWord_4200121) baseStart_4200121 baseEnd_4200121 := by
    simpa [prefixWord, tailWord_4200121, baseEnd_4200121] using wordTrace_append hprefix tailTrace_4200121
  have hstable : (prefixWord ++ tailWord_4200121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200121).length < 2 ^ (prefixWord ++ tailWord_4200121).sum := by decide
  have hdescent : baseEnd_4200121 < baseStart_4200121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200138 : List Nat := [3, 1, 2, 1, 5, 1, 2, 1, 1, 1, 5]
def baseStart_4200138 : Nat := 118140960795 + 4200138 * 2 ^ 59
def prefixEnd_4200138 : Nat := 4983230072969 + 3 ^ 40 * 4200138 * 2
def baseEnd_4200138 : Nat := 2156689609213993174458923

theorem tailTrace_4200138 : CollatzResearch.WordTrace tailWord_4200138 prefixEnd_4200138 2156689609213993174458923 := by
  unfold tailWord_4200138
  simp only [CollatzResearch.WordTrace]
  refine ⟨38297904514406206826558267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102127745371749884870822045 38297904514406206826558267)
  ·
    refine ⟨57446856771609310239837401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38297904514406206826558267 57446856771609310239837401)
    ·
      refine ⟨43085142578706982679878051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57446856771609310239837401 43085142578706982679878051)
      ·
        refine ⟨64627713868060474019817077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43085142578706982679878051 64627713868060474019817077)
        ·
          refine ⟨6058848175130669439357851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64627713868060474019817077 6058848175130669439357851)
          ·
            refine ⟨9088272262696004159036777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6058848175130669439357851 9088272262696004159036777)
            ·
              refine ⟨6816204197022003119277583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9088272262696004159036777 6816204197022003119277583)
              ·
                refine ⟨10224306295533004678916375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6816204197022003119277583 10224306295533004678916375)
                ·
                  refine ⟨15336459443299507018374563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10224306295533004678916375 15336459443299507018374563)
                  ·
                    refine ⟨23004689164949260527561845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15336459443299507018374563 23004689164949260527561845)
                    ·
                      refine ⟨2156689609213993174458923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23004689164949260527561845 2156689609213993174458923)
                      ·
                        rfl

theorem cell23_4200138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_4200138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200138 prefixEnd_4200138 := by exact prefixLift 4200138
  have htrace : WordTrace (prefixWord ++ tailWord_4200138) baseStart_4200138 baseEnd_4200138 := by
    simpa [prefixWord, tailWord_4200138, baseEnd_4200138] using wordTrace_append hprefix tailTrace_4200138
  have hstable : (prefixWord ++ tailWord_4200138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200138).length < 2 ^ (prefixWord ++ tailWord_4200138).sum := by decide
  have hdescent : baseEnd_4200138 < baseStart_4200138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200184 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 3, 8]
def baseStart_4200184 : Nat := 118140960795 + 4200184 * 2 ^ 59
def prefixEnd_4200184 : Nat := 4983230072969 + 3 ^ 40 * 4200184 * 2
def baseEnd_4200184 : Nat := 718904409774699998161237

theorem tailTrace_4200184 : CollatzResearch.WordTrace tailWord_4200184 prefixEnd_4200184 718904409774699998161237 := by
  unfold tailWord_4200184
  simp only [CollatzResearch.WordTrace]
  refine ⟨76596647907729088581203803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102128863876972118108271737 76596647907729088581203803)
  ·
    refine ⟨114894971861593632871805705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76596647907729088581203803 114894971861593632871805705)
    ·
      refine ⟨86171228896195224653854279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114894971861593632871805705 86171228896195224653854279)
      ·
        refine ⟨129256843344292836980781419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86171228896195224653854279 129256843344292836980781419)
        ·
          refine ⟨193885265016439255471172129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129256843344292836980781419 193885265016439255471172129)
          ·
            refine ⟨145413948762329441603379097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193885265016439255471172129 145413948762329441603379097)
            ·
              refine ⟨109060461571747081202534323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145413948762329441603379097 109060461571747081202534323)
              ·
                refine ⟨163590692357620621803801485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109060461571747081202534323 163590692357620621803801485)
                ·
                  refine ⟨61346509634107733176425557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163590692357620621803801485 61346509634107733176425557)
                  ·
                    refine ⟨718904409774699998161237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61346509634107733176425557 718904409774699998161237)
                    ·
                      rfl

theorem cell23_4200184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_4200184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200184 prefixEnd_4200184 := by exact prefixLift 4200184
  have htrace : WordTrace (prefixWord ++ tailWord_4200184) baseStart_4200184 baseEnd_4200184 := by
    simpa [prefixWord, tailWord_4200184, baseEnd_4200184] using wordTrace_append hprefix tailTrace_4200184
  have hstable : (prefixWord ++ tailWord_4200184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200184).length < 2 ^ (prefixWord ++ tailWord_4200184).sum := by decide
  have hdescent : baseEnd_4200184 < baseStart_4200184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200225 : List Nat := [1, 2, 3, 2, 1, 4, 2, 1, 1, 4, 2]
def baseStart_4200225 : Nat := 118140960795 + 4200225 * 2 ^ 59
def prefixEnd_4200225 : Nat := 4983230072969 + 3 ^ 40 * 4200225 * 2
def baseEnd_4200225 : Nat := 2156734282030934334071023

theorem tailTrace_4200225 : CollatzResearch.WordTrace tailWord_4200225 prefixEnd_4200225 2156734282030934334071023 := by
  unfold tailWord_4200225
  simp only [CollatzResearch.WordTrace]
  refine ⟨153194791208309641164650129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102129860805539760776433419 153194791208309641164650129)
  ·
    refine ⟨114896093406232230873487597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153194791208309641164650129 114896093406232230873487597)
    ·
      refine ⟨43086035027337086577557849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114896093406232230873487597 43086035027337086577557849)
      ·
        refine ⟨32314526270502814933168387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43086035027337086577557849 32314526270502814933168387)
        ·
          refine ⟨48471789405754222399752581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32314526270502814933168387 48471789405754222399752581)
          ·
            refine ⟨9088460513578916699953609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48471789405754222399752581 9088460513578916699953609)
            ·
              refine ⟨6816345385184187524965207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9088460513578916699953609 6816345385184187524965207)
              ·
                refine ⟨10224518077776281287447811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6816345385184187524965207 10224518077776281287447811)
                ·
                  refine ⟨15336777116664421931171717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10224518077776281287447811 15336777116664421931171717)
                  ·
                    refine ⟨2875645709374579112094697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15336777116664421931171717 2875645709374579112094697)
                    ·
                      refine ⟨2156734282030934334071023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2875645709374579112094697 2156734282030934334071023)
                      ·
                        rfl

theorem cell23_4200225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_4200225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200225 prefixEnd_4200225 := by exact prefixLift 4200225
  have htrace : WordTrace (prefixWord ++ tailWord_4200225) baseStart_4200225 baseEnd_4200225 := by
    simpa [prefixWord, tailWord_4200225, baseEnd_4200225] using wordTrace_append hprefix tailTrace_4200225
  have hstable : (prefixWord ++ tailWord_4200225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200225).length < 2 ^ (prefixWord ++ tailWord_4200225).sum := by decide
  have hdescent : baseEnd_4200225 < baseStart_4200225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200246 : List Nat := [5, 1, 2, 2, 1, 3, 2, 1, 1, 3, 2]
def baseStart_4200246 : Nat := 118140960795 + 4200246 * 2 ^ 59
def prefixEnd_4200246 : Nat := 4983230072969 + 3 ^ 40 * 4200246 * 2
def baseEnd_4200246 : Nat := 2156745065124678751908427

theorem tailTrace_4200246 : CollatzResearch.WordTrace tailWord_4200246 prefixEnd_4200246 2156745065124678751908427 := by
  unfold tailWord_4200246
  simp only [CollatzResearch.WordTrace]
  refine ⟨9574722321327097609447787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102130371427489041167443061 9574722321327097609447787)
  ·
    refine ⟨14362083481990646414171681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9574722321327097609447787 14362083481990646414171681)
    ·
      refine ⟨10771562611492984810628761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14362083481990646414171681 10771562611492984810628761)
      ·
        refine ⟨8078671958619738607971571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10771562611492984810628761 8078671958619738607971571)
        ·
          refine ⟨12118007937929607911957357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8078671958619738607971571 12118007937929607911957357)
          ·
            refine ⟨4544252976723602966984009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12118007937929607911957357 4544252976723602966984009)
            ·
              refine ⟨3408189732542702225238007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4544252976723602966984009 3408189732542702225238007)
              ·
                refine ⟨5112284598814053337857011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3408189732542702225238007 5112284598814053337857011)
                ·
                  refine ⟨7668426898221080006785517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5112284598814053337857011 7668426898221080006785517)
                  ·
                    refine ⟨2875660086832905002544569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7668426898221080006785517 2875660086832905002544569)
                    ·
                      refine ⟨2156745065124678751908427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2875660086832905002544569 2156745065124678751908427)
                      ·
                        rfl

theorem cell23_4200246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_4200246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200246 prefixEnd_4200246 := by exact prefixLift 4200246
  have htrace : WordTrace (prefixWord ++ tailWord_4200246) baseStart_4200246 baseEnd_4200246 := by
    simpa [prefixWord, tailWord_4200246, baseEnd_4200246] using wordTrace_append hprefix tailTrace_4200246
  have hstable : (prefixWord ++ tailWord_4200246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200246).length < 2 ^ (prefixWord ++ tailWord_4200246).sum := by decide
  have hdescent : baseEnd_4200246 < baseStart_4200246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200248 : List Nat := [2, 1, 2, 1, 3, 3, 1, 5, 5]
def baseStart_4200248 : Nat := 118140960795 + 4200248 * 2 ^ 59
def prefixEnd_4200248 : Nat := 4983230072969 + 3 ^ 40 * 4200248 * 2
def baseEnd_4200248 : Nat := 239638454676220860453713

theorem tailTrace_4200248 : CollatzResearch.WordTrace tailWord_4200248 prefixEnd_4200248 239638454676220860453713 := by
  unfold tailWord_4200248
  simp only [CollatzResearch.WordTrace]
  refine ⟨76597815043613158046368699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102130420058150877395158265 76597815043613158046368699)
  ·
    refine ⟨114896722565419737069553049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76597815043613158046368699 114896722565419737069553049)
    ·
      refine ⟨86172541924064802802164787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114896722565419737069553049 86172541924064802802164787)
      ·
        refine ⟨129258812886097204203247181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86172541924064802802164787 129258812886097204203247181)
        ·
          refine ⟨48472054832286451576217693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129258812886097204203247181 48472054832286451576217693)
          ·
            refine ⟨18177020562107419341081635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48472054832286451576217693 18177020562107419341081635)
            ·
              refine ⟨27265530843161129011622453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18177020562107419341081635 27265530843161129011622453)
              ·
                refine ⟨2556143516546355844839605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27265530843161129011622453 2556143516546355844839605)
                ·
                  refine ⟨239638454676220860453713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2556143516546355844839605 239638454676220860453713)
                  ·
                    rfl

theorem cell23_4200248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5, 5].length) (baseStart_4200248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200248 prefixEnd_4200248 := by exact prefixLift 4200248
  have htrace : WordTrace (prefixWord ++ tailWord_4200248) baseStart_4200248 baseEnd_4200248 := by
    simpa [prefixWord, tailWord_4200248, baseEnd_4200248] using wordTrace_append hprefix tailTrace_4200248
  have hstable : (prefixWord ++ tailWord_4200248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200248).length < 2 ^ (prefixWord ++ tailWord_4200248).sum := by decide
  have hdescent : baseEnd_4200248 < baseStart_4200248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200261 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 4, 5]
def baseStart_4200261 : Nat := 118140960795 + 4200261 * 2 ^ 59
def prefixEnd_4200261 : Nat := 4983230072969 + 3 ^ 40 * 4200261 * 2
def baseEnd_4200261 : Nat := 718917589111498731073619

theorem tailTrace_4200261 : CollatzResearch.WordTrace tailWord_4200261 prefixEnd_4200261 718917589111498731073619 := by
  unfold tailWord_4200261
  simp only [CollatzResearch.WordTrace]
  refine ⟨153196104236179219312960637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102130736157452812875307091 153196104236179219312960637)
  ·
    refine ⟨57448539088567207242360239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153196104236179219312960637 57448539088567207242360239)
    ·
      refine ⟨86172808632850810863540359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57448539088567207242360239 86172808632850810863540359)
      ·
        refine ⟨129259212949276216295310539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86172808632850810863540359 129259212949276216295310539)
        ·
          refine ⟨193888819423914324442965809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129259212949276216295310539 193888819423914324442965809)
          ·
            refine ⟨145416614567935743332224357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193888819423914324442965809 145416614567935743332224357)
            ·
              refine ⟨27265615231487951874792067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145416614567935743332224357 27265615231487951874792067)
              ·
                refine ⟨40898422847231927812188101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27265615231487951874792067 40898422847231927812188101)
                ·
                  refine ⟨7668454283855986464785269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40898422847231927812188101 7668454283855986464785269)
                  ·
                    refine ⟨718917589111498731073619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7668454283855986464785269 718917589111498731073619)
                    ·
                      rfl

theorem cell23_4200261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 5].length) (baseStart_4200261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200261 prefixEnd_4200261 := by exact prefixLift 4200261
  have htrace : WordTrace (prefixWord ++ tailWord_4200261) baseStart_4200261 baseEnd_4200261 := by
    simpa [prefixWord, tailWord_4200261, baseEnd_4200261] using wordTrace_append hprefix tailTrace_4200261
  have hstable : (prefixWord ++ tailWord_4200261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200261).length < 2 ^ (prefixWord ++ tailWord_4200261).sum := by decide
  have hdescent : baseEnd_4200261 < baseStart_4200261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200281 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 3, 3, 4]
def baseStart_4200281 : Nat := 118140960795 + 4200281 * 2 ^ 59
def prefixEnd_4200281 : Nat := 4983230072969 + 3 ^ 40 * 4200281 * 2
def baseEnd_4200281 : Nat := 2156763036947586114970765

theorem tailTrace_4200281 : CollatzResearch.WordTrace tailWord_4200281 prefixEnd_4200281 2156763036947586114970765 := by
  unfold tailWord_4200281
  simp only [CollatzResearch.WordTrace]
  refine ⟨153196833696106762728688697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102131222464071175152459131 153196833696106762728688697)
  ·
    refine ⟨114897625272080072046516523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153196833696106762728688697 114897625272080072046516523)
    ·
      refine ⟨172346437908120108069774785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114897625272080072046516523 172346437908120108069774785)
      ·
        refine ⟨129259828431090081052331089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172346437908120108069774785 129259828431090081052331089)
        ·
          refine ⟨96944871323317560789248317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129259828431090081052331089 96944871323317560789248317)
          ·
            refine ⟨36354326746244085295968119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96944871323317560789248317 36354326746244085295968119)
            ·
              refine ⟨54531490119366127943952179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36354326746244085295968119 54531490119366127943952179)
              ·
                refine ⟨81797235179049191915928269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54531490119366127943952179 81797235179049191915928269)
                ·
                  refine ⟨30673963192143446968473101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81797235179049191915928269 30673963192143446968473101)
                  ·
                    refine ⟨11502736197053792613177413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30673963192143446968473101 11502736197053792613177413)
                    ·
                      refine ⟨2156763036947586114970765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11502736197053792613177413 2156763036947586114970765)
                      ·
                        rfl

theorem cell23_4200281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_4200281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200281 prefixEnd_4200281 := by exact prefixLift 4200281
  have htrace : WordTrace (prefixWord ++ tailWord_4200281) baseStart_4200281 baseEnd_4200281 := by
    simpa [prefixWord, tailWord_4200281, baseEnd_4200281] using wordTrace_append hprefix tailTrace_4200281
  have hstable : (prefixWord ++ tailWord_4200281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200281).length < 2 ^ (prefixWord ++ tailWord_4200281).sum := by decide
  have hdescent : baseEnd_4200281 < baseStart_4200281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200361 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 2, 4, 5]
def baseStart_4200361 : Nat := 118140960795 + 4200361 * 2 ^ 59
def prefixEnd_4200361 : Nat := 4983230072969 + 3 ^ 40 * 4200361 * 2
def baseEnd_4200361 : Nat := 2156804115399945801970397

theorem tailTrace_4200361 : CollatzResearch.WordTrace tailWord_4200361 prefixEnd_4200361 2156804115399945801970397 := by
  unfold tailWord_4200361
  simp only [CollatzResearch.WordTrace]
  refine ⟨153199751535816936391600937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102133167690544624261067291 153199751535816936391600937)
  ·
    refine ⟨114899813651862702293700703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153199751535816936391600937 114899813651862702293700703)
    ·
      refine ⟨172349720477794053440551055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114899813651862702293700703 172349720477794053440551055)
      ·
        refine ⟨258524580716691080160826583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172349720477794053440551055 258524580716691080160826583)
        ·
          refine ⟨387786871075036620241239875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258524580716691080160826583 387786871075036620241239875)
          ·
            refine ⟨581680306612554930361859813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387786871075036620241239875 581680306612554930361859813)
            ·
              refine ⟨109065057489854049442848715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 581680306612554930361859813 109065057489854049442848715)
              ·
                refine ⟨163597586234781074164273073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109065057489854049442848715 163597586234781074164273073)
                ·
                  refine ⟨122698189676085805623204805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163597586234781074164273073 122698189676085805623204805)
                  ·
                    refine ⟨23005910564266088554350901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122698189676085805623204805 23005910564266088554350901)
                    ·
                      refine ⟨2156804115399945801970397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23005910564266088554350901 2156804115399945801970397)
                      ·
                        rfl

theorem cell23_4200361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 4, 5].length) (baseStart_4200361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200361 prefixEnd_4200361 := by exact prefixLift 4200361
  have htrace : WordTrace (prefixWord ++ tailWord_4200361) baseStart_4200361 baseEnd_4200361 := by
    simpa [prefixWord, tailWord_4200361, baseEnd_4200361] using wordTrace_append hprefix tailTrace_4200361
  have hstable : (prefixWord ++ tailWord_4200361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200361).length < 2 ^ (prefixWord ++ tailWord_4200361).sum := by decide
  have hdescent : baseEnd_4200361 < baseStart_4200361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200405 : List Nat := [1, 3, 2, 3, 2, 1, 2, 1, 3, 1, 4]
def baseStart_4200405 : Nat := 118140960795 + 4200405 * 2 ^ 59
def prefixEnd_4200405 : Nat := 4983230072969 + 3 ^ 40 * 4200405 * 2
def baseEnd_4200405 : Nat := 2156826708548743629820195

theorem tailTrace_4200405 : CollatzResearch.WordTrace tailWord_4200405 prefixEnd_4200405 2156826708548743629820195 := by
  unfold tailWord_4200405
  simp only [CollatzResearch.WordTrace]
  refine ⟨153201356347657531906202669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102134237565105021270801779 153201356347657531906202669)
  ·
    refine ⟨57450508630371574464826001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153201356347657531906202669 57450508630371574464826001)
    ·
      refine ⟨43087881472778680848619501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57450508630371574464826001 43087881472778680848619501)
      ·
        refine ⟨16157955552292005318232313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43087881472778680848619501 16157955552292005318232313)
        ·
          refine ⟨12118466664219003988674235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16157955552292005318232313 12118466664219003988674235)
          ·
            refine ⟨18177699996328505983011353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12118466664219003988674235 18177699996328505983011353)
            ·
              refine ⟨13633274997246379487258515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18177699996328505983011353 13633274997246379487258515)
              ·
                refine ⟨20449912495869569230887773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13633274997246379487258515 20449912495869569230887773)
                ·
                  refine ⟨7668717185951088461582915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20449912495869569230887773 7668717185951088461582915)
                  ·
                    refine ⟨11503075778926632692374373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7668717185951088461582915 11503075778926632692374373)
                    ·
                      refine ⟨2156826708548743629820195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11503075778926632692374373 2156826708548743629820195)
                      ·
                        rfl

theorem cell23_4200405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_4200405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200405 prefixEnd_4200405 := by exact prefixLift 4200405
  have htrace : WordTrace (prefixWord ++ tailWord_4200405) baseStart_4200405 baseEnd_4200405 := by
    simpa [prefixWord, tailWord_4200405, baseEnd_4200405] using wordTrace_append hprefix tailTrace_4200405
  have hstable : (prefixWord ++ tailWord_4200405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200405).length < 2 ^ (prefixWord ++ tailWord_4200405).sum := by decide
  have hdescent : baseEnd_4200405 < baseStart_4200405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200409 : List Nat := [1, 2, 1, 2, 6, 2, 1, 1, 2, 3, 2]
def baseStart_4200409 : Nat := 118140960795 + 4200409 * 2 ^ 59
def prefixEnd_4200409 : Nat := 4983230072969 + 3 ^ 40 * 4200409 * 2
def baseEnd_4200409 : Nat := 2156828762471361614170177

theorem tailTrace_4200409 : CollatzResearch.WordTrace tailWord_4200409 prefixEnd_4200409 2156828762471361614170177 := by
  unfold tailWord_4200409
  simp only [CollatzResearch.WordTrace]
  refine ⟨153201502239643040589348281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102134334826428693726232187 153201502239643040589348281)
  ·
    refine ⟨114901126679732280442011211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153201502239643040589348281 114901126679732280442011211)
    ·
      refine ⟨172351690019598420663016817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114901126679732280442011211 172351690019598420663016817)
      ·
        refine ⟨129263767514698815497262613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172351690019598420663016817 129263767514698815497262613)
        ·
          refine ⟨6059239102251506976434185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 129263767514698815497262613 6059239102251506976434185)
          ·
            refine ⟨4544429326688630232325639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6059239102251506976434185 4544429326688630232325639)
            ·
              refine ⟨6816643990032945348488459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4544429326688630232325639 6816643990032945348488459)
              ·
                refine ⟨10224965985049418022732689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6816643990032945348488459 10224965985049418022732689)
                ·
                  refine ⟨7668724488787063517049517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10224965985049418022732689 7668724488787063517049517)
                  ·
                    refine ⟨2875771683295148818893569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7668724488787063517049517 2875771683295148818893569)
                    ·
                      refine ⟨2156828762471361614170177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2875771683295148818893569 2156828762471361614170177)
                      ·
                        rfl

theorem cell23_4200409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 3, 2].length) (baseStart_4200409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200409 prefixEnd_4200409 := by exact prefixLift 4200409
  have htrace : WordTrace (prefixWord ++ tailWord_4200409) baseStart_4200409 baseEnd_4200409 := by
    simpa [prefixWord, tailWord_4200409, baseEnd_4200409] using wordTrace_append hprefix tailTrace_4200409
  have hstable : (prefixWord ++ tailWord_4200409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200409).length < 2 ^ (prefixWord ++ tailWord_4200409).sum := by decide
  have hdescent : baseEnd_4200409 < baseStart_4200409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200452 : List Nat := [2, 3, 2, 4, 1, 1, 1, 1, 1, 1, 6]
def baseStart_4200452 : Nat := 118140960795 + 4200452 * 2 ^ 59
def prefixEnd_4200452 : Nat := 4983230072969 + 3 ^ 40 * 4200452 * 2
def baseEnd_4200452 : Nat := 2156850842139504945932479

theorem tailTrace_4200452 : CollatzResearch.WordTrace tailWord_4200452 prefixEnd_4200452 2156850842139504945932479 := by
  unfold tailWord_4200452
  simp only [CollatzResearch.WordTrace]
  refine ⟨76601535289243629466581805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102135380385658172622109073 76601535289243629466581805)
  ·
    refine ⟨28725575733466361049968177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76601535289243629466581805 28725575733466361049968177)
    ·
      refine ⟨21544181800099770787476133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28725575733466361049968177 21544181800099770787476133)
      ·
        refine ⟨4039534087518707022651775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21544181800099770787476133 4039534087518707022651775)
        ·
          refine ⟨6059301131278060533977663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4039534087518707022651775 6059301131278060533977663)
          ·
            refine ⟨9088951696917090800966495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6059301131278060533977663 9088951696917090800966495)
            ·
              refine ⟨13633427545375636201449743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9088951696917090800966495 13633427545375636201449743)
              ·
                refine ⟨20450141318063454302174615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13633427545375636201449743 20450141318063454302174615)
                ·
                  refine ⟨30675211977095181453261923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20450141318063454302174615 30675211977095181453261923)
                  ·
                    refine ⟨46012817965642772179892885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30675211977095181453261923 46012817965642772179892885)
                    ·
                      refine ⟨2156850842139504945932479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46012817965642772179892885 2156850842139504945932479)
                      ·
                        rfl

theorem cell23_4200452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_4200452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200452 prefixEnd_4200452 := by exact prefixLift 4200452
  have htrace : WordTrace (prefixWord ++ tailWord_4200452) baseStart_4200452 baseEnd_4200452 := by
    simpa [prefixWord, tailWord_4200452, baseEnd_4200452] using wordTrace_append hprefix tailTrace_4200452
  have hstable : (prefixWord ++ tailWord_4200452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200452).length < 2 ^ (prefixWord ++ tailWord_4200452).sum := by decide
  have hdescent : baseEnd_4200452 < baseStart_4200452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200495 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 5, 4, 2]
def baseStart_4200495 : Nat := 118140960795 + 4200495 * 2 ^ 59
def prefixEnd_4200495 : Nat := 4983230072969 + 3 ^ 40 * 4200495 * 2
def baseEnd_4200495 : Nat := 2156872921807648277694781

theorem tailTrace_4200495 : CollatzResearch.WordTrace tailWord_4200495 prefixEnd_4200495 2156872921807648277694781 := by
  unfold tailWord_4200495
  simp only [CollatzResearch.WordTrace]
  refine ⟨153204638917331477276978939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102136425944887651517985959 153204638917331477276978939)
  ·
    refine ⟨229806958375997215915468409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153204638917331477276978939 229806958375997215915468409)
    ·
      refine ⟨172355218781997911936601307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229806958375997215915468409 172355218781997911936601307)
      ·
        refine ⟨258532828172996867904901961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172355218781997911936601307 258532828172996867904901961)
        ·
          refine ⟨193899621129747650928676471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258532828172996867904901961 193899621129747650928676471)
          ·
            refine ⟨290849431694621476393014707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193899621129747650928676471 290849431694621476393014707)
            ·
              refine ⟨436274147541932214589522061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290849431694621476393014707 436274147541932214589522061)
              ·
                refine ⟨163602805328224580471070773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 436274147541932214589522061 163602805328224580471070773)
                ·
                  refine ⟨15337762999521054419162885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 163602805328224580471070773 15337762999521054419162885)
                  ·
                    refine ⟨2875830562410197703593041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15337762999521054419162885 2875830562410197703593041)
                    ·
                      refine ⟨2156872921807648277694781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2875830562410197703593041 2156872921807648277694781)
                      ·
                        rfl

theorem cell23_4200495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 4, 2].length) (baseStart_4200495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200495 prefixEnd_4200495 := by exact prefixLift 4200495
  have htrace : WordTrace (prefixWord ++ tailWord_4200495) baseStart_4200495 baseEnd_4200495 := by
    simpa [prefixWord, tailWord_4200495, baseEnd_4200495] using wordTrace_append hprefix tailTrace_4200495
  have hstable : (prefixWord ++ tailWord_4200495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200495).length < 2 ^ (prefixWord ++ tailWord_4200495).sum := by decide
  have hdescent : baseEnd_4200495 < baseStart_4200495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200545 : List Nat := [1, 2, 3, 1, 1, 2, 1, 4, 2, 3, 3]
def baseStart_4200545 : Nat := 118140960795 + 4200545 * 2 ^ 59
def prefixEnd_4200545 : Nat := 4983230072969 + 3 ^ 40 * 4200545 * 2
def baseEnd_4200545 : Nat := 2156898595840373082069551

theorem tailTrace_4200545 : CollatzResearch.WordTrace tailWord_4200545 prefixEnd_4200545 2156898595840373082069551 := by
  unfold tailWord_4200545
  simp only [CollatzResearch.WordTrace]
  refine ⟨153206462567150335816299089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102137641711433557210866059 153206462567150335816299089)
  ·
    refine ⟨114904846925362751862224317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153206462567150335816299089 114904846925362751862224317)
    ·
      refine ⟨43089317597011031948334119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114904846925362751862224317 43089317597011031948334119)
      ·
        refine ⟨64633976395516547922501179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43089317597011031948334119 64633976395516547922501179)
        ·
          refine ⟨96950964593274821883751769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64633976395516547922501179 96950964593274821883751769)
          ·
            refine ⟨72713223444956116412813827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96950964593274821883751769 72713223444956116412813827)
            ·
              refine ⟨109069835167434174619220741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72713223444956116412813827 109069835167434174619220741)
              ·
                refine ⟨20450594093893907741103889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109069835167434174619220741 20450594093893907741103889)
                ·
                  refine ⟨15337945570420430805827917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20450594093893907741103889 15337945570420430805827917)
                  ·
                    refine ⟨5751729588907661552185469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15337945570420430805827917 5751729588907661552185469)
                    ·
                      refine ⟨2156898595840373082069551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5751729588907661552185469 2156898595840373082069551)
                      ·
                        rfl

theorem cell23_4200545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_4200545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200545 prefixEnd_4200545 := by exact prefixLift 4200545
  have htrace : WordTrace (prefixWord ++ tailWord_4200545) baseStart_4200545 baseEnd_4200545 := by
    simpa [prefixWord, tailWord_4200545, baseEnd_4200545] using wordTrace_append hprefix tailTrace_4200545
  have hstable : (prefixWord ++ tailWord_4200545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200545).length < 2 ^ (prefixWord ++ tailWord_4200545).sum := by decide
  have hdescent : baseEnd_4200545 < baseStart_4200545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200562 : List Nat := [3, 2, 1, 2, 2, 3, 1, 1, 2, 3, 3]
def baseStart_4200562 : Nat := 118140960795 + 4200562 * 2 ^ 59
def prefixEnd_4200562 : Nat := 4983230072969 + 3 ^ 40 * 4200562 * 2
def baseEnd_4200562 : Nat := 2156907325011499515556973

theorem tailTrace_4200562 : CollatzResearch.WordTrace tailWord_4200562 prefixEnd_4200562 2156907325011499515556973 := by
  unfold tailWord_4200562
  simp only [CollatzResearch.WordTrace]
  refine ⟨38301770652022186929916985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102138055072059165146445293 38301770652022186929916985)
  ·
    refine ⟨28726327989016640197437739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38301770652022186929916985 28726327989016640197437739)
    ·
      refine ⟨43089491983524960296156609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28726327989016640197437739 43089491983524960296156609)
      ·
        refine ⟨32317118987643720222117457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43089491983524960296156609 32317118987643720222117457)
        ·
          refine ⟨24237839240732790166588093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32317118987643720222117457 24237839240732790166588093)
          ·
            refine ⟨9089189715274796312470535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24237839240732790166588093 9089189715274796312470535)
            ·
              refine ⟨13633784572912194468705803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9089189715274796312470535 13633784572912194468705803)
              ·
                refine ⟨20450676859368291703058705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13633784572912194468705803 20450676859368291703058705)
                ·
                  refine ⟨15338007644526218777294029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20450676859368291703058705 15338007644526218777294029)
                  ·
                    refine ⟨5751752866697332041485261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15338007644526218777294029 5751752866697332041485261)
                    ·
                      refine ⟨2156907325011499515556973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5751752866697332041485261 2156907325011499515556973)
                      ·
                        rfl

theorem cell23_4200562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_4200562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200562 prefixEnd_4200562 := by exact prefixLift 4200562
  have htrace : WordTrace (prefixWord ++ tailWord_4200562) baseStart_4200562 baseEnd_4200562 := by
    simpa [prefixWord, tailWord_4200562, baseEnd_4200562] using wordTrace_append hprefix tailTrace_4200562
  have hstable : (prefixWord ++ tailWord_4200562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200562).length < 2 ^ (prefixWord ++ tailWord_4200562).sum := by decide
  have hdescent : baseEnd_4200562 < baseStart_4200562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200585 : List Nat := [1, 2, 1, 1, 4, 2, 3, 1, 1, 3, 4]
def baseStart_4200585 : Nat := 118140960795 + 4200585 * 2 ^ 59
def prefixEnd_4200585 : Nat := 4983230072969 + 3 ^ 40 * 4200585 * 2
def baseEnd_4200585 : Nat := 2156919135066552925569367

theorem tailTrace_4200585 : CollatzResearch.WordTrace tailWord_4200585 prefixEnd_4200585 2156919135066552925569367 := by
  unfold tailWord_4200585
  simp only [CollatzResearch.WordTrace]
  refine ⟨153207921487005422647755209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102138614324670281765170139 153207921487005422647755209)
  ·
    refine ⟨114905941115254066985816407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153207921487005422647755209 114905941115254066985816407)
    ·
      refine ⟨172358911672881100478724611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114905941115254066985816407 172358911672881100478724611)
      ·
        refine ⟨258538367509321650718086917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172358911672881100478724611 258538367509321650718086917)
        ·
          refine ⟨48475943907997809509641297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 258538367509321650718086917 48475943907997809509641297)
          ·
            refine ⟨36356957930998357132230973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48475943907997809509641297 36356957930998357132230973)
            ·
              refine ⟨13633859224124383924586615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36356957930998357132230973 13633859224124383924586615)
              ·
                refine ⟨20450788836186575886879923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13633859224124383924586615 20450788836186575886879923)
                ·
                  refine ⟨30676183254279863830319885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20450788836186575886879923 30676183254279863830319885)
                  ·
                    refine ⟨11503568720354948936369957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30676183254279863830319885 11503568720354948936369957)
                    ·
                      refine ⟨2156919135066552925569367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11503568720354948936369957 2156919135066552925569367)
                      ·
                        rfl

theorem cell23_4200585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 3, 4].length) (baseStart_4200585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200585 prefixEnd_4200585 := by exact prefixLift 4200585
  have htrace : WordTrace (prefixWord ++ tailWord_4200585) baseStart_4200585 baseEnd_4200585 := by
    simpa [prefixWord, tailWord_4200585, baseEnd_4200585] using wordTrace_append hprefix tailTrace_4200585
  have hstable : (prefixWord ++ tailWord_4200585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200585).length < 2 ^ (prefixWord ++ tailWord_4200585).sum := by decide
  have hdescent : baseEnd_4200585 < baseStart_4200585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200595 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 7, 4]
def baseStart_4200595 : Nat := 118140960795 + 4200595 * 2 ^ 59
def prefixEnd_4200595 : Nat := 4983230072969 + 3 ^ 40 * 4200595 * 2
def baseEnd_4200595 : Nat := 718974756624365962148107

theorem tailTrace_4200595 : CollatzResearch.WordTrace tailWord_4200595 prefixEnd_4200595 718974756624365962148107 := by
  unfold tailWord_4200595
  simp only [CollatzResearch.WordTrace]
  refine ⟨153208286216969194355619239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102138857477979462903746159 153208286216969194355619239)
  ·
    refine ⟨229812429325453791533428859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153208286216969194355619239 229812429325453791533428859)
    ·
      refine ⟨344718643988180687300143289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229812429325453791533428859 344718643988180687300143289)
      ·
        refine ⟨258538982991135515475107467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344718643988180687300143289 258538982991135515475107467)
        ·
          refine ⟨387808474486703273212661201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258538982991135515475107467 387808474486703273212661201)
          ·
            refine ⟨290856355865027454909495901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387808474486703273212661201 290856355865027454909495901)
            ·
              refine ⟨109071133449385295591060963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290856355865027454909495901 109071133449385295591060963)
              ·
                refine ⟨163606700174077943386591445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109071133449385295591060963 163606700174077943386591445)
                ·
                  refine ⟨3834532035329951798123237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 163606700174077943386591445 3834532035329951798123237)
                  ·
                    refine ⟨718974756624365962148107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3834532035329951798123237 718974756624365962148107)
                    ·
                      rfl

theorem cell23_4200595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7, 4].length) (baseStart_4200595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200595 prefixEnd_4200595 := by exact prefixLift 4200595
  have htrace : WordTrace (prefixWord ++ tailWord_4200595) baseStart_4200595 baseEnd_4200595 := by
    simpa [prefixWord, tailWord_4200595, baseEnd_4200595] using wordTrace_append hprefix tailTrace_4200595
  have hstable : (prefixWord ++ tailWord_4200595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200595).length < 2 ^ (prefixWord ++ tailWord_4200595).sum := by decide
  have hdescent : baseEnd_4200595 < baseStart_4200595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200635 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 2, 5, 3]
def baseStart_4200635 : Nat := 118140960795 + 4200635 * 2 ^ 59
def prefixEnd_4200635 : Nat := 4983230072969 + 3 ^ 40 * 4200635 * 2
def baseEnd_4200635 : Nat := 2156944809099277729944137

theorem tailTrace_4200635 : CollatzResearch.WordTrace tailWord_4200635 prefixEnd_4200635 2156944809099277729944137 := by
  unfold tailWord_4200635
  simp only [CollatzResearch.WordTrace]
  refine ⟨153209745136824281187075359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102139830091216187458050239 153209745136824281187075359)
  ·
    refine ⟨229814617705236421780613039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153209745136824281187075359 229814617705236421780613039)
    ·
      refine ⟨344721926557854632670919559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229814617705236421780613039 344721926557854632670919559)
      ·
        refine ⟨517082889836781949006379339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344721926557854632670919559 517082889836781949006379339)
        ·
          refine ⟨775624334755172923509569009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 517082889836781949006379339 775624334755172923509569009)
          ·
            refine ⟨581718251066379692632176757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 775624334755172923509569009 581718251066379692632176757)
            ·
              refine ⟨54536086037473096184266571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 581718251066379692632176757 54536086037473096184266571)
              ·
                refine ⟨81804129056209644276399857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54536086037473096184266571 81804129056209644276399857)
                ·
                  refine ⟨61353096792157233207299893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81804129056209644276399857 61353096792157233207299893)
                  ·
                    refine ⟨5751852824264740613184365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61353096792157233207299893 5751852824264740613184365)
                    ·
                      refine ⟨2156944809099277729944137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5751852824264740613184365 2156944809099277729944137)
                      ·
                        rfl

theorem cell23_4200635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5, 3].length) (baseStart_4200635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200635 prefixEnd_4200635 := by exact prefixLift 4200635
  have htrace : WordTrace (prefixWord ++ tailWord_4200635) baseStart_4200635 baseEnd_4200635 := by
    simpa [prefixWord, tailWord_4200635, baseEnd_4200635] using wordTrace_append hprefix tailTrace_4200635
  have hstable : (prefixWord ++ tailWord_4200635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200635).length < 2 ^ (prefixWord ++ tailWord_4200635).sum := by decide
  have hdescent : baseEnd_4200635 < baseStart_4200635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200709 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 7, 2, 2]
def baseStart_4200709 : Nat := 118140960795 + 4200709 * 2 ^ 59
def prefixEnd_4200709 : Nat := 4983230072969 + 3 ^ 40 * 4200709 * 2
def baseEnd_4200709 : Nat := 2156982806667710440418797

theorem tailTrace_4200709 : CollatzResearch.WordTrace tailWord_4200709 prefixEnd_4200709 2156982806667710440418797 := by
  unfold tailWord_4200709
  simp only [CollatzResearch.WordTrace]
  refine ⟨153212444138556191825269181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102141629425704127883512787 153212444138556191825269181)
  ·
    refine ⟨57454666551958571934475943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153212444138556191825269181 57454666551958571934475943)
    ·
      refine ⟨86181999827937857901713915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57454666551958571934475943 86181999827937857901713915)
      ·
        refine ⟨129272999741906786852570873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86181999827937857901713915 129272999741906786852570873)
        ·
          refine ⟨96954749806430090139428155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129272999741906786852570873 96954749806430090139428155)
          ·
            refine ⟨145432124709645135209142233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96954749806430090139428155 145432124709645135209142233)
            ·
              refine ⟨109074093532233851406856675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145432124709645135209142233 109074093532233851406856675)
              ·
                refine ⟨163611140298350777110285013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109074093532233851406856675 163611140298350777110285013)
                ·
                  refine ⟨3834636100742596338522305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 163611140298350777110285013 3834636100742596338522305)
                  ·
                    refine ⟨2875977075556947253891729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3834636100742596338522305 2875977075556947253891729)
                    ·
                      refine ⟨2156982806667710440418797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2875977075556947253891729 2156982806667710440418797)
                      ·
                        rfl

theorem cell23_4200709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7, 2, 2].length) (baseStart_4200709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200709 prefixEnd_4200709 := by exact prefixLift 4200709
  have htrace : WordTrace (prefixWord ++ tailWord_4200709) baseStart_4200709 baseEnd_4200709 := by
    simpa [prefixWord, tailWord_4200709, baseEnd_4200709] using wordTrace_append hprefix tailTrace_4200709
  have hstable : (prefixWord ++ tailWord_4200709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200709).length < 2 ^ (prefixWord ++ tailWord_4200709).sum := by decide
  have hdescent : baseEnd_4200709 < baseStart_4200709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200776 : List Nat := [2, 1, 3, 1, 1, 2, 5, 2, 2, 1, 3]
def baseStart_4200776 : Nat := 118140960795 + 4200776 * 2 ^ 59
def prefixEnd_4200776 : Nat := 4983230072969 + 3 ^ 40 * 4200776 * 2
def baseEnd_4200776 : Nat := 2157017209871561678280989

theorem tailTrace_4200776 : CollatzResearch.WordTrace tailWord_4200776 prefixEnd_4200776 2157017209871561678280989 := by
  unfold tailWord_4200776
  simp only [CollatzResearch.WordTrace]
  refine ⟨76607443914656731133979091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102143258552875641511972121 76607443914656731133979091)
  ·
    refine ⟨114911165871985096700968637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76607443914656731133979091 114911165871985096700968637)
    ·
      refine ⟨43091687201994411262863239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114911165871985096700968637 43091687201994411262863239)
      ·
        refine ⟨64637530802991616894294859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43091687201994411262863239 64637530802991616894294859)
        ·
          refine ⟨96956296204487425341442289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64637530802991616894294859 96956296204487425341442289)
          ·
            refine ⟨72717222153365569006081717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96956296204487425341442289 72717222153365569006081717)
            ·
              refine ⟨6817239576878022094320161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72717222153365569006081717 6817239576878022094320161)
              ·
                refine ⟨5112929682658516570740121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6817239576878022094320161 5112929682658516570740121)
                ·
                  refine ⟨3834697261993887428055091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5112929682658516570740121 3834697261993887428055091)
                  ·
                    refine ⟨5752045892990831142082637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3834697261993887428055091 5752045892990831142082637)
                    ·
                      refine ⟨2157017209871561678280989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5752045892990831142082637 2157017209871561678280989)
                      ·
                        rfl

theorem cell23_4200776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_4200776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200776 prefixEnd_4200776 := by exact prefixLift 4200776
  have htrace : WordTrace (prefixWord ++ tailWord_4200776) baseStart_4200776 baseEnd_4200776 := by
    simpa [prefixWord, tailWord_4200776, baseEnd_4200776] using wordTrace_append hprefix tailTrace_4200776
  have hstable : (prefixWord ++ tailWord_4200776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200776).length < 2 ^ (prefixWord ++ tailWord_4200776).sum := by decide
  have hdescent : baseEnd_4200776 < baseStart_4200776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200782 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4]
def baseStart_4200782 : Nat := 118140960795 + 4200782 * 2 ^ 59
def prefixEnd_4200782 : Nat := 4983230072969 + 3 ^ 40 * 4200782 * 2
def baseEnd_4200782 : Nat := 2157020290755488654805961

theorem tailTrace_4200782 : CollatzResearch.WordTrace tailWord_4200782 prefixEnd_4200782 2157020290755488654805961 := by
  unfold tailWord_4200782
  simp only [CollatzResearch.WordTrace]
  refine ⟨19151888333411465661584575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102143404444861150195117733 19151888333411465661584575)
  ·
    refine ⟨28727832500117198492376863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19151888333411465661584575 28727832500117198492376863)
    ·
      refine ⟨43091748750175797738565295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28727832500117198492376863 43091748750175797738565295)
      ·
        refine ⟨64637623125263696607847943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43091748750175797738565295 64637623125263696607847943)
        ·
          refine ⟨96956434687895544911771915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64637623125263696607847943 96956434687895544911771915)
          ·
            refine ⟨145434652031843317367657873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96956434687895544911771915 145434652031843317367657873)
            ·
              refine ⟨109075989023882488025743405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145434652031843317367657873 109075989023882488025743405)
              ·
                refine ⟨40903495883955933009653777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109075989023882488025743405 40903495883955933009653777)
                ·
                  refine ⟨30677621912966949757240333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40903495883955933009653777 30677621912966949757240333)
                  ·
                    refine ⟨11504108217362606158965125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30677621912966949757240333 11504108217362606158965125)
                    ·
                      refine ⟨2157020290755488654805961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11504108217362606158965125 2157020290755488654805961)
                      ·
                        rfl

theorem cell23_4200782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_4200782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200782 prefixEnd_4200782 := by exact prefixLift 4200782
  have htrace : WordTrace (prefixWord ++ tailWord_4200782) baseStart_4200782 baseEnd_4200782 := by
    simpa [prefixWord, tailWord_4200782, baseEnd_4200782] using wordTrace_append hprefix tailTrace_4200782
  have hstable : (prefixWord ++ tailWord_4200782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200782).length < 2 ^ (prefixWord ++ tailWord_4200782).sum := by decide
  have hdescent : baseEnd_4200782 < baseStart_4200782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200816 : List Nat := [2, 1, 1, 1, 4, 3, 1, 2, 4, 2, 2]
def baseStart_4200816 : Nat := 118140960795 + 4200816 * 2 ^ 59
def prefixEnd_4200816 : Nat := 4983230072969 + 3 ^ 40 * 4200816 * 2
def baseEnd_4200816 : Nat := 2157037749097741521780805

theorem tailTrace_4200816 : CollatzResearch.WordTrace tailWord_4200816 prefixEnd_4200816 2157037749097741521780805 := by
  unfold tailWord_4200816
  simp only [CollatzResearch.WordTrace]
  refine ⟨76608173374584274549707151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102144231166112366066276201 76608173374584274549707151)
  ·
    refine ⟨114912260061876411824560727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76608173374584274549707151 114912260061876411824560727)
    ·
      refine ⟨172368390092814617736841091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114912260061876411824560727 172368390092814617736841091)
      ·
        refine ⟨258552585139221926605261637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172368390092814617736841091 258552585139221926605261637)
        ·
          refine ⟨48478609713604111238486557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 258552585139221926605261637 48478609713604111238486557)
          ·
            refine ⟨18179478642601541714432459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48478609713604111238486557 18179478642601541714432459)
            ·
              refine ⟨27269217963902312571648689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18179478642601541714432459 27269217963902312571648689)
              ·
                refine ⟨20451913472926734428736517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27269217963902312571648689 20451913472926734428736517)
                ·
                  refine ⟨3834733776173762705388097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20451913472926734428736517 3834733776173762705388097)
                  ·
                    refine ⟨2876050332130322029041073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3834733776173762705388097 2876050332130322029041073)
                    ·
                      refine ⟨2157037749097741521780805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2876050332130322029041073 2157037749097741521780805)
                      ·
                        rfl

theorem cell23_4200816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 4, 2, 2].length) (baseStart_4200816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200816 prefixEnd_4200816 := by exact prefixLift 4200816
  have htrace : WordTrace (prefixWord ++ tailWord_4200816) baseStart_4200816 baseEnd_4200816 := by
    simpa [prefixWord, tailWord_4200816, baseEnd_4200816] using wordTrace_append hprefix tailTrace_4200816
  have hstable : (prefixWord ++ tailWord_4200816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200816).length < 2 ^ (prefixWord ++ tailWord_4200816).sum := by decide
  have hdescent : baseEnd_4200816 < baseStart_4200816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200833 : List Nat := [1, 2, 4, 3, 1, 1, 2, 1, 4, 2, 2]
def baseStart_4200833 : Nat := 118140960795 + 4200833 * 2 ^ 59
def prefixEnd_4200833 : Nat := 4983230072969 + 3 ^ 40 * 4200833 * 2
def baseEnd_4200833 : Nat := 2157046478268867955268227

theorem tailTrace_4200833 : CollatzResearch.WordTrace tailWord_4200833 prefixEnd_4200833 2157046478268867955268227 := by
  unfold tailWord_4200833
  simp only [CollatzResearch.WordTrace]
  refine ⟨153216966790106961002783153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102144644526737974001855435 153216966790106961002783153)
  ·
    refine ⟨114912725092580220752087365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153216966790106961002783153 114912725092580220752087365)
    ·
      refine ⟨21546135954858791391016381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114912725092580220752087365 21546135954858791391016381)
      ·
        refine ⟨8079800983072046771631143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21546135954858791391016381 8079800983072046771631143)
        ·
          refine ⟨12119701474608070157446715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8079800983072046771631143 12119701474608070157446715)
          ·
            refine ⟨18179552211912105236170073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12119701474608070157446715 18179552211912105236170073)
            ·
              refine ⟨13634664158934078927127555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18179552211912105236170073 13634664158934078927127555)
              ·
                refine ⟨20451996238401118390691333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13634664158934078927127555 20451996238401118390691333)
                ·
                  refine ⟨3834749294700209698254625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20451996238401118390691333 3834749294700209698254625)
                  ·
                    refine ⟨2876061971025157273690969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3834749294700209698254625 2876061971025157273690969)
                    ·
                      refine ⟨2157046478268867955268227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2876061971025157273690969 2157046478268867955268227)
                      ·
                        rfl

theorem cell23_4200833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_4200833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200833 prefixEnd_4200833 := by exact prefixLift 4200833
  have htrace : WordTrace (prefixWord ++ tailWord_4200833) baseStart_4200833 baseEnd_4200833 := by
    simpa [prefixWord, tailWord_4200833, baseEnd_4200833] using wordTrace_append hprefix tailTrace_4200833
  have hstable : (prefixWord ++ tailWord_4200833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200833).length < 2 ^ (prefixWord ++ tailWord_4200833).sum := by decide
  have hdescent : baseEnd_4200833 < baseStart_4200833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200869 : List Nat := [1, 3, 1, 2, 1, 1, 6, 1, 2, 5]
def baseStart_4200869 : Nat := 118140960795 + 4200869 * 2 ^ 59
def prefixEnd_4200869 : Nat := 4983230072969 + 3 ^ 40 * 4200869 * 2
def baseEnd_4200869 : Nat := 719021654524143271472687

theorem tailTrace_4200869 : CollatzResearch.WordTrace tailWord_4200869 prefixEnd_4200869 719021654524143271472687 := by
  unfold tailWord_4200869
  simp only [CollatzResearch.WordTrace]
  refine ⟨153218279817976539151093661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102145519878651026100729107 153218279817976539151093661)
  ·
    refine ⟨57456854931741202181660123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153218279817976539151093661 57456854931741202181660123)
    ·
      refine ⟨86185282397611803272490185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57456854931741202181660123 86185282397611803272490185)
      ·
        refine ⟨64638961798208852454367639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86185282397611803272490185 64638961798208852454367639)
        ·
          refine ⟨96958442697313278681551459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64638961798208852454367639 96958442697313278681551459)
          ·
            refine ⟨145437664045969918022327189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96958442697313278681551459 145437664045969918022327189)
            ·
              refine ⟨6817390502154839907296587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 145437664045969918022327189 6817390502154839907296587)
              ·
                refine ⟨10226085753232259860944881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6817390502154839907296587 10226085753232259860944881)
                ·
                  refine ⟨7669564314924194895708661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10226085753232259860944881 7669564314924194895708661)
                  ·
                    refine ⟨719021654524143271472687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7669564314924194895708661 719021654524143271472687)
                    ·
                      rfl

theorem cell23_4200869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 5].length) (baseStart_4200869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200869 prefixEnd_4200869 := by exact prefixLift 4200869
  have htrace : WordTrace (prefixWord ++ tailWord_4200869) baseStart_4200869 baseEnd_4200869 := by
    simpa [prefixWord, tailWord_4200869, baseEnd_4200869] using wordTrace_append hprefix tailTrace_4200869
  have hstable : (prefixWord ++ tailWord_4200869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200869).length < 2 ^ (prefixWord ++ tailWord_4200869).sum := by decide
  have hdescent : baseEnd_4200869 < baseStart_4200869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200884 : List Nat := [2, 5, 2, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_4200884 : Nat := 118140960795 + 4200884 * 2 ^ 59
def prefixEnd_4200884 : Nat := 4983230072969 + 3 ^ 40 * 4200884 * 2
def baseEnd_4200884 : Nat := 2157072665782247255730493

theorem tailTrace_4200884 : CollatzResearch.WordTrace tailWord_4200884 prefixEnd_4200884 2157072665782247255730493 := by
  unfold tailWord_4200884
  simp only [CollatzResearch.WordTrace]
  refine ⟨76609413456461098356444853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102145884608614797808593137 76609413456461098356444853)
  ·
    refine ⟨7182132511543227970916705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76609413456461098356444853 7182132511543227970916705)
    ·
      refine ⟨5386599383657420978187529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7182132511543227970916705 5386599383657420978187529)
      ·
        refine ⟨4039949537743065733640647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5386599383657420978187529 4039949537743065733640647)
        ·
          refine ⟨6059924306614598600460971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4039949537743065733640647 6059924306614598600460971)
          ·
            refine ⟨9089886459921897900691457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6059924306614598600460971 9089886459921897900691457)
            ·
              refine ⟨6817414844941423425518593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9089886459921897900691457 6817414844941423425518593)
              ·
                refine ⟨5113061133706067569138945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6817414844941423425518593 5113061133706067569138945)
                ·
                  refine ⟨3834795850279550676854209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5113061133706067569138945 3834795850279550676854209)
                  ·
                    refine ⟨2876096887709663007640657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3834795850279550676854209 2876096887709663007640657)
                    ·
                      refine ⟨2157072665782247255730493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2876096887709663007640657 2157072665782247255730493)
                      ·
                        rfl

theorem cell23_4200884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_4200884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200884 prefixEnd_4200884 := by exact prefixLift 4200884
  have htrace : WordTrace (prefixWord ++ tailWord_4200884) baseStart_4200884 baseEnd_4200884 := by
    simpa [prefixWord, tailWord_4200884, baseEnd_4200884] using wordTrace_append hprefix tailTrace_4200884
  have hstable : (prefixWord ++ tailWord_4200884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200884).length < 2 ^ (prefixWord ++ tailWord_4200884).sum := by decide
  have hdescent : baseEnd_4200884 < baseStart_4200884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200899 : List Nat := [1, 1, 1, 3, 1, 1, 3, 5, 3, 4]
def baseStart_4200899 : Nat := 118140960795 + 4200899 * 2 ^ 59
def prefixEnd_4200899 : Nat := 4983230072969 + 3 ^ 40 * 4200899 * 2
def baseEnd_4200899 : Nat := 719026789330688232347641

theorem tailTrace_4200899 : CollatzResearch.WordTrace tailWord_4200899 prefixEnd_4200899 719026789330688232347641 := by
  unfold tailWord_4200899
  simp only [CollatzResearch.WordTrace]
  refine ⟨153219374007867854274685751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102146249338578569516457167 153219374007867854274685751)
  ·
    refine ⟨229829061011801781412028627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153219374007867854274685751 229829061011801781412028627)
    ·
      refine ⟨344743591517702672118042941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229829061011801781412028627 344743591517702672118042941)
      ·
        refine ⟨129278846819138502044266103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 344743591517702672118042941 129278846819138502044266103)
        ·
          refine ⟨193918270228707753066399155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129278846819138502044266103 193918270228707753066399155)
          ·
            refine ⟨290877405343061629599598733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193918270228707753066399155 290877405343061629599598733)
            ·
              refine ⟨109079027003648111099849525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290877405343061629599598733 109079027003648111099849525)
              ·
                refine ⟨10226158781592010415610893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109079027003648111099849525 10226158781592010415610893)
                ·
                  refine ⟨3834809543097003905854085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10226158781592010415610893 3834809543097003905854085)
                  ·
                    refine ⟨719026789330688232347641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3834809543097003905854085 719026789330688232347641)
                    ·
                      rfl

theorem cell23_4200899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3, 4].length) (baseStart_4200899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200899 prefixEnd_4200899 := by exact prefixLift 4200899
  have htrace : WordTrace (prefixWord ++ tailWord_4200899) baseStart_4200899 baseEnd_4200899 := by
    simpa [prefixWord, tailWord_4200899, baseEnd_4200899] using wordTrace_append hprefix tailTrace_4200899
  have hstable : (prefixWord ++ tailWord_4200899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200899).length < 2 ^ (prefixWord ++ tailWord_4200899).sum := by decide
  have hdescent : baseEnd_4200899 < baseStart_4200899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200906 : List Nat := [3, 1, 2, 1, 2, 2, 3, 1, 2, 4, 2]
def baseStart_4200906 : Nat := 118140960795 + 4200906 * 2 ^ 59
def prefixEnd_4200906 : Nat := 4983230072969 + 3 ^ 40 * 4200906 * 2
def baseEnd_4200906 : Nat := 2157083962356646169655391

theorem tailTrace_4200906 : CollatzResearch.WordTrace tailWord_4200906 prefixEnd_4200906 2157083962356646169655391 := by
  unfold tailWord_4200906
  simp only [CollatzResearch.WordTrace]
  refine ⟨38304907329710623617547643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102146419545894996313460381 38304907329710623617547643)
  ·
    refine ⟨57457360994565935426321465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38304907329710623617547643 57457360994565935426321465)
    ·
      refine ⟨43093020745924451569741099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57457360994565935426321465 43093020745924451569741099)
      ·
        refine ⟨64639531118886677354611649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43093020745924451569741099 64639531118886677354611649)
        ·
          refine ⟨48479648339165008015958737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64639531118886677354611649 48479648339165008015958737)
          ·
            refine ⟨36359736254373756011969053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48479648339165008015958737 36359736254373756011969053)
            ·
              refine ⟨13634901095390158504488395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36359736254373756011969053 13634901095390158504488395)
              ·
                refine ⟨20452351643085237756732593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13634901095390158504488395 20452351643085237756732593)
                ·
                  refine ⟨15339263732313928317549445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20452351643085237756732593 15339263732313928317549445)
                  ·
                    refine ⟨2876111949808861559540521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15339263732313928317549445 2876111949808861559540521)
                    ·
                      refine ⟨2157083962356646169655391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2876111949808861559540521 2157083962356646169655391)
                      ·
                        rfl

theorem cell23_4200906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 2, 4, 2].length) (baseStart_4200906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200906 prefixEnd_4200906 := by exact prefixLift 4200906
  have htrace : WordTrace (prefixWord ++ tailWord_4200906) baseStart_4200906 baseEnd_4200906 := by
    simpa [prefixWord, tailWord_4200906, baseEnd_4200906] using wordTrace_append hprefix tailTrace_4200906
  have hstable : (prefixWord ++ tailWord_4200906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200906).length < 2 ^ (prefixWord ++ tailWord_4200906).sum := by decide
  have hdescent : baseEnd_4200906 < baseStart_4200906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200916 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 5, 4]
def baseStart_4200916 : Nat := 118140960795 + 4200916 * 2 ^ 59
def prefixEnd_4200916 : Nat := 4983230072969 + 3 ^ 40 * 4200916 * 2
def baseEnd_4200916 : Nat := 719029699054397043510115

theorem tailTrace_4200916 : CollatzResearch.WordTrace tailWord_4200916 prefixEnd_4200916 719029699054397043510115 := by
  unfold tailWord_4200916
  simp only [CollatzResearch.WordTrace]
  refine ⟨76609997024403133089027301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102146662699204177452036401 76609997024403133089027301)
  ·
    refine ⟨14364374442075587454192619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76609997024403133089027301 14364374442075587454192619)
    ·
      refine ⟨21546561663113381181288929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14364374442075587454192619 21546561663113381181288929)
      ·
        refine ⟨16159921247335035885966697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21546561663113381181288929 16159921247335035885966697)
        ·
          refine ⟨12119940935501276914475023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16159921247335035885966697 12119940935501276914475023)
          ·
            refine ⟨18179911403251915371712535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12119940935501276914475023 18179911403251915371712535)
            ·
              refine ⟨27269867104877873057568803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18179911403251915371712535 27269867104877873057568803)
              ·
                refine ⟨40904800657316809586353205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27269867104877873057568803 40904800657316809586353205)
                ·
                  refine ⟨3834825061623450898720613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40904800657316809586353205 3834825061623450898720613)
                  ·
                    refine ⟨719029699054397043510115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3834825061623450898720613 719029699054397043510115)
                    ·
                      rfl

theorem cell23_4200916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_4200916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200916 prefixEnd_4200916 := by exact prefixLift 4200916
  have htrace : WordTrace (prefixWord ++ tailWord_4200916) baseStart_4200916 baseEnd_4200916 := by
    simpa [prefixWord, tailWord_4200916, baseEnd_4200916] using wordTrace_append hprefix tailTrace_4200916
  have hstable : (prefixWord ++ tailWord_4200916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200916).length < 2 ^ (prefixWord ++ tailWord_4200916).sum := by decide
  have hdescent : baseEnd_4200916 < baseStart_4200916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4200946 : List Nat := [3, 2, 1, 4, 2, 1, 1, 1, 8]
def baseStart_4200946 : Nat := 118140960795 + 4200946 * 2 ^ 59
def prefixEnd_4200946 : Nat := 4983230072969 + 3 ^ 40 * 4200946 * 2
def baseEnd_4200946 : Nat := 239678277953647334795023

theorem tailTrace_4200946 : CollatzResearch.WordTrace tailWord_4200946 prefixEnd_4200946 239678277953647334795023 := by
  unfold tailWord_4200946
  simp only [CollatzResearch.WordTrace]
  refine ⟨38305272059674395325411673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102147392159131720867764461 38305272059674395325411673)
  ·
    refine ⟨28728954044755796494058755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38305272059674395325411673 28728954044755796494058755)
    ·
      refine ⟨43093431067133694741088133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28728954044755796494058755 43093431067133694741088133)
      ·
        refine ⟨8080018325087567763954025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43093431067133694741088133 8080018325087567763954025)
        ·
          refine ⟨6060013743815675822965519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8080018325087567763954025 6060013743815675822965519)
          ·
            refine ⟨9090020615723513734448279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6060013743815675822965519 9090020615723513734448279)
            ·
              refine ⟨13635030923585270601672419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9090020615723513734448279 13635030923585270601672419)
              ·
                refine ⟨20452546385377905902508629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13635030923585270601672419 20452546385377905902508629)
                ·
                  refine ⟨239678277953647334795023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20452546385377905902508629 239678277953647334795023)
                  ·
                    rfl

theorem cell23_4200946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 8].length) (baseStart_4200946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4200946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4200946 prefixEnd_4200946 := by exact prefixLift 4200946
  have htrace : WordTrace (prefixWord ++ tailWord_4200946) baseStart_4200946 baseEnd_4200946 := by
    simpa [prefixWord, tailWord_4200946, baseEnd_4200946] using wordTrace_append hprefix tailTrace_4200946
  have hstable : (prefixWord ++ tailWord_4200946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4200946).length < 2 ^ (prefixWord ++ tailWord_4200946).sum := by decide
  have hdescent : baseEnd_4200946 < baseStart_4200946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4200946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201000 : List Nat := [2, 1, 5, 2, 1, 2, 1, 2, 2, 3, 2]
def baseStart_4201000 : Nat := 118140960795 + 4201000 * 2 ^ 59
def prefixEnd_4201000 : Nat := 4983230072969 + 3 ^ 40 * 4201000 * 2
def baseEnd_4201000 : Nat := 2157132229538168801879959

theorem tailTrace_4201000 : CollatzResearch.WordTrace tailWord_4201000 prefixEnd_4201000 2157132229538168801879959 := by
  unfold tailWord_4201000
  simp only [CollatzResearch.WordTrace]
  refine ⟨76611528890250974262056227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102148705187001299016074969 76611528890250974262056227)
  ·
    refine ⟨114917293335376461393084341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76611528890250974262056227 114917293335376461393084341)
    ·
      refine ⟨10773496250191543255601657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114917293335376461393084341 10773496250191543255601657)
      ·
        refine ⟨8080122187643657441701243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10773496250191543255601657 8080122187643657441701243)
        ·
          refine ⟨12120183281465486162551865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8080122187643657441701243 12120183281465486162551865)
          ·
            refine ⟨9090137461099114621913899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12120183281465486162551865 9090137461099114621913899)
            ·
              refine ⟨13635206191648671932870849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9090137461099114621913899 13635206191648671932870849)
              ·
                refine ⟨10226404643736503949653137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13635206191648671932870849 10226404643736503949653137)
                ·
                  refine ⟨7669803482802377962239853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10226404643736503949653137 7669803482802377962239853)
                  ·
                    refine ⟨2876176306050891735839945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7669803482802377962239853 2876176306050891735839945)
                    ·
                      refine ⟨2157132229538168801879959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2876176306050891735839945 2157132229538168801879959)
                      ·
                        rfl

theorem cell23_4201000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_4201000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201000 prefixEnd_4201000 := by exact prefixLift 4201000
  have htrace : WordTrace (prefixWord ++ tailWord_4201000) baseStart_4201000 baseEnd_4201000 := by
    simpa [prefixWord, tailWord_4201000, baseEnd_4201000] using wordTrace_append hprefix tailTrace_4201000
  have hstable : (prefixWord ++ tailWord_4201000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201000).length < 2 ^ (prefixWord ++ tailWord_4201000).sum := by decide
  have hdescent : baseEnd_4201000 < baseStart_4201000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201009 : List Nat := [1, 2, 2, 3, 1, 1, 3, 2, 1, 1, 6]
def baseStart_4201009 : Nat := 118140960795 + 4201009 * 2 ^ 59
def prefixEnd_4201009 : Nat := 4983230072969 + 3 ^ 40 * 4201009 * 2
def baseEnd_4201009 : Nat := 2157136850864059266667417

theorem tailTrace_4201009 : CollatzResearch.WordTrace tailWord_4201009 prefixEnd_4201009 2157136850864059266667417 := by
  unfold tailWord_4201009
  simp only [CollatzResearch.WordTrace]
  refine ⟨153223386037469343061190081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102148924024979562040793387 153223386037469343061190081)
  ·
    refine ⟨114917539528102007295892561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153223386037469343061190081 114917539528102007295892561)
    ·
      refine ⟨86188154646076505471919421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114917539528102007295892561 86188154646076505471919421)
      ·
        refine ⟨32320557992278689551969783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86188154646076505471919421 32320557992278689551969783)
        ·
          refine ⟨48480836988418034327954675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32320557992278689551969783 48480836988418034327954675)
          ·
            refine ⟨72721255482627051491932013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48480836988418034327954675 72721255482627051491932013)
            ·
              refine ⟨27270470805985144309474505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72721255482627051491932013 27270470805985144309474505)
              ·
                refine ⟨20452853104488858232105879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27270470805985144309474505 20452853104488858232105879)
                ·
                  refine ⟨30679279656733287348158819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20452853104488858232105879 30679279656733287348158819)
                  ·
                    refine ⟨46018919485099931022238229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30679279656733287348158819 46018919485099931022238229)
                    ·
                      refine ⟨2157136850864059266667417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46018919485099931022238229 2157136850864059266667417)
                      ·
                        rfl

theorem cell23_4201009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_4201009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201009 prefixEnd_4201009 := by exact prefixLift 4201009
  have htrace : WordTrace (prefixWord ++ tailWord_4201009) baseStart_4201009 baseEnd_4201009 := by
    simpa [prefixWord, tailWord_4201009, baseEnd_4201009] using wordTrace_append hprefix tailTrace_4201009
  have hstable : (prefixWord ++ tailWord_4201009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201009).length < 2 ^ (prefixWord ++ tailWord_4201009).sum := by decide
  have hdescent : baseEnd_4201009 < baseStart_4201009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201016 : List Nat := [2, 1, 2, 1, 4, 1, 2, 2, 3, 2, 3]
def baseStart_4201016 : Nat := 118140960795 + 4201016 * 2 ^ 59
def prefixEnd_4201016 : Nat := 4983230072969 + 3 ^ 40 * 4201016 * 2
def baseEnd_4201016 : Nat := 2157140445228640739279885

theorem tailTrace_4201016 : CollatzResearch.WordTrace tailWord_4201016 prefixEnd_4201016 2157140445228640739279885 := by
  unfold tailWord_4201016
  simp only [CollatzResearch.WordTrace]
  refine ⟨76611820674221991628347451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102149094232295988837796601 76611820674221991628347451)
  ·
    refine ⟨114917731011332987442521177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76611820674221991628347451 114917731011332987442521177)
    ·
      refine ⟨86188298258499740581890883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114917731011332987442521177 86188298258499740581890883)
      ·
        refine ⟨129282447387749610872836325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86188298258499740581890883 129282447387749610872836325)
        ·
          refine ⟨24240458885203052038656811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129282447387749610872836325 24240458885203052038656811)
          ·
            refine ⟨36360688327804578057985217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24240458885203052038656811 36360688327804578057985217)
            ·
              refine ⟨27270516245853433543488913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36360688327804578057985217 27270516245853433543488913)
              ·
                refine ⟨20452887184390075157616685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27270516245853433543488913 20452887184390075157616685)
                ·
                  refine ⟨7669832694146278184106257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20452887184390075157616685 7669832694146278184106257)
                  ·
                    refine ⟨5752374520609708638079693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7669832694146278184106257 5752374520609708638079693)
                    ·
                      refine ⟨2157140445228640739279885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5752374520609708638079693 2157140445228640739279885)
                      ·
                        rfl

theorem cell23_4201016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 3, 2, 3].length) (baseStart_4201016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201016 prefixEnd_4201016 := by exact prefixLift 4201016
  have htrace : WordTrace (prefixWord ++ tailWord_4201016) baseStart_4201016 baseEnd_4201016 := by
    simpa [prefixWord, tailWord_4201016, baseEnd_4201016] using wordTrace_append hprefix tailTrace_4201016
  have hstable : (prefixWord ++ tailWord_4201016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201016).length < 2 ^ (prefixWord ++ tailWord_4201016).sum := by decide
  have hdescent : baseEnd_4201016 < baseStart_4201016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201030 : List Nat := [6, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_4201030 : Nat := 118140960795 + 4201030 * 2 ^ 59
def prefixEnd_4201030 : Nat := 4983230072969 + 3 ^ 40 * 4201030 * 2
def baseEnd_4201030 : Nat := 2157147633957803684504821

theorem tailTrace_4201030 : CollatzResearch.WordTrace tailWord_4201030 prefixEnd_4201030 2157147633957803684504821 := by
  unfold tailWord_4201030
  simp only [CollatzResearch.WordTrace]
  refine ⟨4788254749074789488990767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 102149434646928842431803029 4788254749074789488990767)
  ·
    refine ⟨7182382123612184233486151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4788254749074789488990767 7182382123612184233486151)
    ·
      refine ⟨10773573185418276350229227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7182382123612184233486151 10773573185418276350229227)
      ·
        refine ⟨16160359778127414525343841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10773573185418276350229227 16160359778127414525343841)
        ·
          refine ⟨12120269833595560894007881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16160359778127414525343841 12120269833595560894007881)
          ·
            refine ⟨9090202375196670670505911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12120269833595560894007881 9090202375196670670505911)
            ·
              refine ⟨13635303562795006005758867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9090202375196670670505911 13635303562795006005758867)
              ·
                refine ⟨20452955344192509008638301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13635303562795006005758867 20452955344192509008638301)
                ·
                  refine ⟨7669858254072190878239363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20452955344192509008638301 7669858254072190878239363)
                  ·
                    refine ⟨11504787381108286317359045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7669858254072190878239363 11504787381108286317359045)
                    ·
                      refine ⟨2157147633957803684504821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11504787381108286317359045 2157147633957803684504821)
                      ·
                        rfl

theorem cell23_4201030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_4201030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201030 prefixEnd_4201030 := by exact prefixLift 4201030
  have htrace : WordTrace (prefixWord ++ tailWord_4201030) baseStart_4201030 baseEnd_4201030 := by
    simpa [prefixWord, tailWord_4201030, baseEnd_4201030] using wordTrace_append hprefix tailTrace_4201030
  have hstable : (prefixWord ++ tailWord_4201030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201030).length < 2 ^ (prefixWord ++ tailWord_4201030).sum := by decide
  have hdescent : baseEnd_4201030 < baseStart_4201030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201058 : List Nat := [3, 3, 2, 3, 2, 1, 2, 2, 1, 1, 3]
def baseStart_4201058 : Nat := 118140960795 + 4201058 * 2 ^ 59
def prefixEnd_4201058 : Nat := 4983230072969 + 3 ^ 40 * 4201058 * 2
def baseEnd_4201058 : Nat := 2157162011416129574954693

theorem tailTrace_4201058 : CollatzResearch.WordTrace tailWord_4201058 prefixEnd_4201058 2157162011416129574954693 := by
  unfold tailWord_4201058
  simp only [CollatzResearch.WordTrace]
  refine ⟨38306293303572956107430957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102150115476194549619815885 38306293303572956107430957)
  ·
    refine ⟨14364859988839858540286609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38306293303572956107430957 14364859988839858540286609)
    ·
      refine ⟨10773644991629893905214957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14364859988839858540286609 10773644991629893905214957)
      ·
        refine ⟨4040116871861210214455609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10773644991629893905214957 4040116871861210214455609)
        ·
          refine ⟨3030087653895907660841707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4040116871861210214455609 3030087653895907660841707)
          ·
            refine ⟨4545131480843861491262561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3030087653895907660841707 4545131480843861491262561)
            ·
              refine ⟨3408848610632896118446921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4545131480843861491262561 3408848610632896118446921)
              ·
                refine ⟨2556636457974672088835191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3408848610632896118446921 2556636457974672088835191)
                ·
                  refine ⟨3834954686962008133252787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2556636457974672088835191 3834954686962008133252787)
                  ·
                    refine ⟨5752432030443012199879181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3834954686962008133252787 5752432030443012199879181)
                    ·
                      refine ⟨2157162011416129574954693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5752432030443012199879181 2157162011416129574954693)
                      ·
                        rfl

theorem cell23_4201058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_4201058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201058 prefixEnd_4201058 := by exact prefixLift 4201058
  have htrace : WordTrace (prefixWord ++ tailWord_4201058) baseStart_4201058 baseEnd_4201058 := by
    simpa [prefixWord, tailWord_4201058, baseEnd_4201058] using wordTrace_append hprefix tailTrace_4201058
  have hstable : (prefixWord ++ tailWord_4201058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201058).length < 2 ^ (prefixWord ++ tailWord_4201058).sum := by decide
  have hdescent : baseEnd_4201058 < baseStart_4201058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201064 : List Nat := [2, 1, 4, 3, 2, 1, 1, 4, 1, 2, 2]
def baseStart_4201064 : Nat := 118140960795 + 4201064 * 2 ^ 59
def prefixEnd_4201064 : Nat := 4983230072969 + 3 ^ 40 * 4201064 * 2
def baseEnd_4201064 : Nat := 2157165092300056551479665

theorem tailTrace_4201064 : CollatzResearch.WordTrace tailWord_4201064 prefixEnd_4201064 2157165092300056551479665 := by
  unfold tailWord_4201064
  simp only [CollatzResearch.WordTrace]
  refine ⟨76612696026135043727221123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102150261368180058302961497 76612696026135043727221123)
  ·
    refine ⟨114919044039202565590831685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76612696026135043727221123 114919044039202565590831685)
    ·
      refine ⟨21547320757350481048280941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114919044039202565590831685 21547320757350481048280941)
      ·
        refine ⟨8080245284006430393105353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21547320757350481048280941 8080245284006430393105353)
        ·
          refine ⟨6060183963004822794829015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8080245284006430393105353 6060183963004822794829015)
          ·
            refine ⟨9090275944507234192243523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6060183963004822794829015 9090275944507234192243523)
            ·
              refine ⟨13635413916760851288365285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9090275944507234192243523 13635413916760851288365285)
              ·
                refine ⟨2556640109392659616568491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13635413916760851288365285 2556640109392659616568491)
                ·
                  refine ⟨3834960164088989424852737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2556640109392659616568491 3834960164088989424852737)
                  ·
                    refine ⟨2876220123066742068639553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3834960164088989424852737 2876220123066742068639553)
                    ·
                      refine ⟨2157165092300056551479665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2876220123066742068639553 2157165092300056551479665)
                      ·
                        rfl

theorem cell23_4201064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_4201064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201064 prefixEnd_4201064 := by exact prefixLift 4201064
  have htrace : WordTrace (prefixWord ++ tailWord_4201064) baseStart_4201064 baseEnd_4201064 := by
    simpa [prefixWord, tailWord_4201064, baseEnd_4201064] using wordTrace_append hprefix tailTrace_4201064
  have hstable : (prefixWord ++ tailWord_4201064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201064).length < 2 ^ (prefixWord ++ tailWord_4201064).sum := by decide
  have hdescent : baseEnd_4201064 < baseStart_4201064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201079 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 1, 8]
def baseStart_4201079 : Nat := 118140960795 + 4201079 * 2 ^ 59
def prefixEnd_4201079 : Nat := 4983230072969 + 3 ^ 40 * 4201079 * 2
def baseEnd_4201079 : Nat := 719057598169957997597365

theorem tailTrace_4201079 : CollatzResearch.WordTrace tailWord_4201079 prefixEnd_4201079 719057598169957997597365 := by
  unfold tailWord_4201079
  simp only [CollatzResearch.WordTrace]
  refine ⟨153225939147215745016238291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102150626098143830010825527 153225939147215745016238291)
  ·
    refine ⟨229838908720823617524357437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153225939147215745016238291 229838908720823617524357437)
    ·
      refine ⟨86189590770308856571634039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229838908720823617524357437 86189590770308856571634039)
      ·
        refine ⟨129284386155463284857451059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86189590770308856571634039 129284386155463284857451059)
        ·
          refine ⟨193926579233194927286176589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129284386155463284857451059 193926579233194927286176589)
          ·
            refine ⟨72722467212448097732316221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193926579233194927286176589 72722467212448097732316221)
            ·
              refine ⟨27270925204668036649618583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72722467212448097732316221 27270925204668036649618583)
              ·
                refine ⟨40906387807002054974427875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27270925204668036649618583 40906387807002054974427875)
                ·
                  refine ⟨61359581710503082461641813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40906387807002054974427875 61359581710503082461641813)
                  ·
                    refine ⟨719057598169957997597365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61359581710503082461641813 719057598169957997597365)
                    ·
                      rfl

theorem cell23_4201079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_4201079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201079 prefixEnd_4201079 := by exact prefixLift 4201079
  have htrace : WordTrace (prefixWord ++ tailWord_4201079) baseStart_4201079 baseEnd_4201079 := by
    simpa [prefixWord, tailWord_4201079, baseEnd_4201079] using wordTrace_append hprefix tailTrace_4201079
  have hstable : (prefixWord ++ tailWord_4201079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201079).length < 2 ^ (prefixWord ++ tailWord_4201079).sum := by decide
  have hdescent : baseEnd_4201079 < baseStart_4201079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201103 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 6, 2, 2]
def baseStart_4201103 : Nat := 118140960795 + 4201103 * 2 ^ 59
def prefixEnd_4201103 : Nat := 4983230072969 + 3 ^ 40 * 4201103 * 2
def baseEnd_4201103 : Nat := 2157185118045581898891985

theorem tailTrace_4201103 : CollatzResearch.WordTrace tailWord_4201103 prefixEnd_4201103 2157185118045581898891985 := by
  unfold tailWord_4201103
  simp only [CollatzResearch.WordTrace]
  refine ⟨153226814499128797115111963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102151209666085864743407975 153226814499128797115111963)
  ·
    refine ⟨229840221748693195672667945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153226814499128797115111963 229840221748693195672667945)
    ·
      refine ⟨172380166311519896754500959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229840221748693195672667945 172380166311519896754500959)
      ·
        refine ⟨258570249467279845131751439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172380166311519896754500959 258570249467279845131751439)
        ·
          refine ⟨387855374200919767697627159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258570249467279845131751439 387855374200919767697627159)
          ·
            refine ⟨581783061301379651546440739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387855374200919767697627159 581783061301379651546440739)
            ·
              refine ⟨872674591952069477319661109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581783061301379651546440739 872674591952069477319661109)
              ·
                refine ⟨81813242995506513498718229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 872674591952069477319661109 81813242995506513498718229)
                ·
                  refine ⟨3834995765414367820252417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81813242995506513498718229 3834995765414367820252417)
                  ·
                    refine ⟨2876246824060775865189313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3834995765414367820252417 2876246824060775865189313)
                    ·
                      refine ⟨2157185118045581898891985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2876246824060775865189313 2157185118045581898891985)
                      ·
                        rfl

theorem cell23_4201103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6, 2, 2].length) (baseStart_4201103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201103 prefixEnd_4201103 := by exact prefixLift 4201103
  have htrace : WordTrace (prefixWord ++ tailWord_4201103) baseStart_4201103 baseEnd_4201103 := by
    simpa [prefixWord, tailWord_4201103, baseEnd_4201103] using wordTrace_append hprefix tailTrace_4201103
  have hstable : (prefixWord ++ tailWord_4201103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201103).length < 2 ^ (prefixWord ++ tailWord_4201103).sum := by decide
  have hdescent : baseEnd_4201103 < baseStart_4201103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201114 : List Nat := [3, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3]
def baseStart_4201114 : Nat := 118140960795 + 4201114 * 2 ^ 59
def prefixEnd_4201114 : Nat := 4983230072969 + 3 ^ 40 * 4201114 * 2
def baseEnd_4201114 : Nat := 2157190766332781355854435

theorem tailTrace_4201114 : CollatzResearch.WordTrace tailWord_4201114 prefixEnd_4201114 2157190766332781355854435 := by
  unfold tailWord_4201114
  simp only [CollatzResearch.WordTrace]
  refine ⟨38306803925522236498440599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102151477134725963995841597 38306803925522236498440599)
  ·
    refine ⟨57460205888283354747660899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38306803925522236498440599 57460205888283354747660899)
    ·
      refine ⟨86190308832425032121491349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57460205888283354747660899 86190308832425032121491349)
      ·
        refine ⟨4040170726519923380694907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 86190308832425032121491349 4040170726519923380694907)
        ·
          refine ⟨6060256089779885071042361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4040170726519923380694907 6060256089779885071042361)
          ·
            refine ⟨4545192067334913803281771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6060256089779885071042361 4545192067334913803281771)
            ·
              refine ⟨6817788101002370704922657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4545192067334913803281771 6817788101002370704922657)
              ·
                refine ⟨5113341075751778028691993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6817788101002370704922657 5113341075751778028691993)
                ·
                  refine ⟨3835005806813833521518995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5113341075751778028691993 3835005806813833521518995)
                  ·
                    refine ⟨5752508710220750282278493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3835005806813833521518995 5752508710220750282278493)
                    ·
                      refine ⟨2157190766332781355854435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5752508710220750282278493 2157190766332781355854435)
                      ·
                        rfl

theorem cell23_4201114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_4201114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201114 prefixEnd_4201114 := by exact prefixLift 4201114
  have htrace : WordTrace (prefixWord ++ tailWord_4201114) baseStart_4201114 baseEnd_4201114 := by
    simpa [prefixWord, tailWord_4201114, baseEnd_4201114] using wordTrace_append hprefix tailTrace_4201114
  have hstable : (prefixWord ++ tailWord_4201114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201114).length < 2 ^ (prefixWord ++ tailWord_4201114).sum := by decide
  have hdescent : baseEnd_4201114 < baseStart_4201114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201129 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 8]
def baseStart_4201129 : Nat := 118140960795 + 4201129 * 2 ^ 59
def prefixEnd_4201129 : Nat := 4983230072969 + 3 ^ 40 * 4201129 * 2
def baseEnd_4201129 : Nat := 2157198468542598797166865

theorem tailTrace_4201129 : CollatzResearch.WordTrace tailWord_4201129 prefixEnd_4201129 2157198468542598797166865 := by
  unfold tailWord_4201129
  simp only [CollatzResearch.WordTrace]
  refine ⟨153227762797034603555558441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102151841864689735703705627 153227762797034603555558441)
  ·
    refine ⟨114920822097775952666668831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153227762797034603555558441 114920822097775952666668831)
    ·
      refine ⟨172381233146663929000003247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114920822097775952666668831 172381233146663929000003247)
      ·
        refine ⟨258571849719995893500004871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172381233146663929000003247 258571849719995893500004871)
        ·
          refine ⟨387857774579993840250007307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258571849719995893500004871 387857774579993840250007307)
          ·
            refine ⟨581786661869990760375010961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387857774579993840250007307 581786661869990760375010961)
            ·
              refine ⟨436339996402493070281258221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 581786661869990760375010961 436339996402493070281258221)
              ·
                refine ⟨163627498650934901355471833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 436339996402493070281258221 163627498650934901355471833)
                ·
                  refine ⟨122720623988201176016603875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163627498650934901355471833 122720623988201176016603875)
                  ·
                    refine ⟨184080935982301764024905813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 122720623988201176016603875 184080935982301764024905813)
                    ·
                      refine ⟨2157198468542598797166865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 184080935982301764024905813 2157198468542598797166865)
                      ·
                        rfl

theorem cell23_4201129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_4201129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201129 prefixEnd_4201129 := by exact prefixLift 4201129
  have htrace : WordTrace (prefixWord ++ tailWord_4201129) baseStart_4201129 baseEnd_4201129 := by
    simpa [prefixWord, tailWord_4201129, baseEnd_4201129] using wordTrace_append hprefix tailTrace_4201129
  have hstable : (prefixWord ++ tailWord_4201129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201129).length < 2 ^ (prefixWord ++ tailWord_4201129).sum := by decide
  have hdescent : baseEnd_4201129 < baseStart_4201129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201133 : List Nat := [1, 5, 2, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_4201133 : Nat := 118140960795 + 4201133 * 2 ^ 59
def prefixEnd_4201133 : Nat := 4983230072969 + 3 ^ 40 * 4201133 * 2
def baseEnd_4201133 : Nat := 2157200522465216781516847

theorem tailTrace_4201133 : CollatzResearch.WordTrace tailWord_4201133 prefixEnd_4201133 2157200522465216781516847 := by
  unfold tailWord_4201133
  simp only [CollatzResearch.WordTrace]
  refine ⟨153227908689020112238704053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102151939126013408159136035 153227908689020112238704053)
  ·
    refine ⟨14365116439595635522378505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 153227908689020112238704053 14365116439595635522378505)
    ·
      refine ⟨10773837329696726641783879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14365116439595635522378505 10773837329696726641783879)
      ·
        refine ⟨16160755994545089962675819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10773837329696726641783879 16160755994545089962675819)
        ·
          refine ⟨24241133991817634944013729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16160755994545089962675819 24241133991817634944013729)
          ·
            refine ⟨18180850493863226208010297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24241133991817634944013729 18180850493863226208010297)
            ·
              refine ⟨13635637870397419656007723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18180850493863226208010297 13635637870397419656007723)
              ·
                refine ⟨20453456805596129484011585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13635637870397419656007723 20453456805596129484011585)
                ·
                  refine ⟨15340092604197097113008689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20453456805596129484011585 15340092604197097113008689)
                  ·
                    refine ⟨11505069453147822834756517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15340092604197097113008689 11505069453147822834756517)
                    ·
                      refine ⟨2157200522465216781516847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11505069453147822834756517 2157200522465216781516847)
                      ·
                        rfl

theorem cell23_4201133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_4201133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201133 prefixEnd_4201133 := by exact prefixLift 4201133
  have htrace : WordTrace (prefixWord ++ tailWord_4201133) baseStart_4201133 baseEnd_4201133 := by
    simpa [prefixWord, tailWord_4201133, baseEnd_4201133] using wordTrace_append hprefix tailTrace_4201133
  have hstable : (prefixWord ++ tailWord_4201133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201133).length < 2 ^ (prefixWord ++ tailWord_4201133).sum := by decide
  have hdescent : baseEnd_4201133 < baseStart_4201133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201160 : List Nat := [2, 1, 3, 1, 2, 5, 1, 3, 5]
def baseStart_4201160 : Nat := 118140960795 + 4201160 * 2 ^ 59
def prefixEnd_4201160 : Nat := 4983230072969 + 3 ^ 40 * 4201160 * 2
def baseEnd_4201160 : Nat := 239690487382543130653247

theorem tailTrace_4201160 : CollatzResearch.WordTrace tailWord_4201160 prefixEnd_4201160 239690487382543130653247 := by
  unfold tailWord_4201160
  simp only [CollatzResearch.WordTrace]
  refine ⟨76614446729961147924968467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102152595639948197233291289 76614446729961147924968467)
  ·
    refine ⟨114921670094941721887452701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76614446729961147924968467 114921670094941721887452701)
    ·
      refine ⟨43095626285603145707794763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114921670094941721887452701 43095626285603145707794763)
      ·
        refine ⟨64643439428404718561692145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43095626285603145707794763 64643439428404718561692145)
        ·
          refine ⟨48482579571303538921269109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64643439428404718561692145 48482579571303538921269109)
          ·
            refine ⟨4545241834809706773868979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48482579571303538921269109 4545241834809706773868979)
            ·
              refine ⟨6817862752214560160803469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4545241834809706773868979 6817862752214560160803469)
              ·
                refine ⟨2556698532080460060301301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6817862752214560160803469 2556698532080460060301301)
                ·
                  refine ⟨239690487382543130653247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2556698532080460060301301 239690487382543130653247)
                  ·
                    rfl

theorem cell23_4201160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3, 5].length) (baseStart_4201160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201160 prefixEnd_4201160 := by exact prefixLift 4201160
  have htrace : WordTrace (prefixWord ++ tailWord_4201160) baseStart_4201160 baseEnd_4201160 := by
    simpa [prefixWord, tailWord_4201160, baseEnd_4201160] using wordTrace_append hprefix tailTrace_4201160
  have hstable : (prefixWord ++ tailWord_4201160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201160).length < 2 ^ (prefixWord ++ tailWord_4201160).sum := by decide
  have hdescent : baseEnd_4201160 < baseStart_4201160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201193 : List Nat := [1, 2, 1, 1, 1, 2, 4, 3, 2, 4, 2]
def baseStart_4201193 : Nat := 118140960795 + 4201193 * 2 ^ 59
def prefixEnd_4201193 : Nat := 4983230072969 + 3 ^ 40 * 4201193 * 2
def baseEnd_4201193 : Nat := 2157231331304486546766571

theorem tailTrace_4201193 : CollatzResearch.WordTrace tailWord_4201193 prefixEnd_4201193 2157231331304486546766571 := by
  unfold tailWord_4201193
  simp only [CollatzResearch.WordTrace]
  refine ⟨153230097068802742485888233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102153398045868494990592155 153230097068802742485888233)
  ·
    refine ⟨114922572801602056864416175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153230097068802742485888233 114922572801602056864416175)
    ·
      refine ⟨172383859202403085296624263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114922572801602056864416175 172383859202403085296624263)
      ·
        refine ⟨258575788803604627944936395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172383859202403085296624263 258575788803604627944936395)
        ·
          refine ⟨387863683205406941917404593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258575788803604627944936395 387863683205406941917404593)
          ·
            refine ⟨290897762404055206438053445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387863683205406941917404593 290897762404055206438053445)
            ·
              refine ⟨54543330450760351207135021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 290897762404055206438053445 54543330450760351207135021)
              ·
                refine ⟨20453748919035131702675633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54543330450760351207135021 20453748919035131702675633)
                ·
                  refine ⟨15340311689276348777006725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20453748919035131702675633 15340311689276348777006725)
                  ·
                    refine ⟨2876308441739315395688761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15340311689276348777006725 2876308441739315395688761)
                    ·
                      refine ⟨2157231331304486546766571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2876308441739315395688761 2157231331304486546766571)
                      ·
                        rfl

theorem cell23_4201193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 4, 2].length) (baseStart_4201193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201193 prefixEnd_4201193 := by exact prefixLift 4201193
  have htrace : WordTrace (prefixWord ++ tailWord_4201193) baseStart_4201193 baseEnd_4201193 := by
    simpa [prefixWord, tailWord_4201193, baseEnd_4201193] using wordTrace_append hprefix tailTrace_4201193
  have hstable : (prefixWord ++ tailWord_4201193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201193).length < 2 ^ (prefixWord ++ tailWord_4201193).sum := by decide
  have hdescent : baseEnd_4201193 < baseStart_4201193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201260 : List Nat := [2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 3]
def baseStart_4201260 : Nat := 118140960795 + 4201260 * 2 ^ 59
def prefixEnd_4201260 : Nat := 4983230072969 + 3 ^ 40 * 4201260 * 2
def baseEnd_4201260 : Nat := 2157265734508337784628763

theorem tailTrace_4201260 : CollatzResearch.WordTrace tailWord_4201260 prefixEnd_4201260 2157265734508337784628763 := by
  unfold tailWord_4201260
  simp only [CollatzResearch.WordTrace]
  refine ⟨76616270379780006464288617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102155027173040008619051489 76616270379780006464288617)
  ·
    refine ⟨57462202784835004848216463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76616270379780006464288617 57462202784835004848216463)
    ·
      refine ⟨86193304177252507272324695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57462202784835004848216463 86193304177252507272324695)
      ·
        refine ⟨129289956265878760908487043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86193304177252507272324695 129289956265878760908487043)
        ·
          refine ⟨193934934398818141362730565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129289956265878760908487043 193934934398818141362730565)
          ·
            refine ⟨36362800199778401505511981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193934934398818141362730565 36362800199778401505511981)
            ·
              refine ⟨13636050074916900564566993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36362800199778401505511981 13636050074916900564566993)
              ·
                refine ⟨10227037556187675423425245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13636050074916900564566993 10227037556187675423425245)
                ·
                  refine ⟨3835139083570378283784467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10227037556187675423425245 3835139083570378283784467)
                  ·
                    refine ⟨5752708625355567425676701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3835139083570378283784467 5752708625355567425676701)
                    ·
                      refine ⟨2157265734508337784628763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5752708625355567425676701 2157265734508337784628763)
                      ·
                        rfl

theorem cell23_4201260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 3].length) (baseStart_4201260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201260 prefixEnd_4201260 := by exact prefixLift 4201260
  have htrace : WordTrace (prefixWord ++ tailWord_4201260) baseStart_4201260 baseEnd_4201260 := by
    simpa [prefixWord, tailWord_4201260, baseEnd_4201260] using wordTrace_append hprefix tailTrace_4201260
  have hstable : (prefixWord ++ tailWord_4201260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201260).length < 2 ^ (prefixWord ++ tailWord_4201260).sum := by decide
  have hdescent : baseEnd_4201260 < baseStart_4201260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201261 : List Nat := [1, 5, 3, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_4201261 : Nat := 118140960795 + 4201261 * 2 ^ 59
def prefixEnd_4201261 : Nat := 4983230072969 + 3 ^ 40 * 4201261 * 2
def baseEnd_4201261 : Nat := 2157266247988992280716259

theorem tailTrace_4201261 : CollatzResearch.WordTrace tailWord_4201261 prefixEnd_4201261 2157266247988992280716259 := by
  unfold tailWord_4201261
  simp only [CollatzResearch.WordTrace]
  refine ⟨153232577232556390099363637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102155051488370926732909091 153232577232556390099363637)
  ·
    refine ⟨14365554115552161571815341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 153232577232556390099363637 14365554115552161571815341)
    ·
      refine ⟨5387082793332060589430753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14365554115552161571815341 5387082793332060589430753)
      ·
        refine ⟨4040312094999045442073065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5387082793332060589430753 4040312094999045442073065)
        ·
          refine ⟨3030234071249284081554799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4040312094999045442073065 3030234071249284081554799)
          ·
            refine ⟨4545351106873926122332199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3030234071249284081554799 4545351106873926122332199)
            ·
              refine ⟨6818026660310889183498299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4545351106873926122332199 6818026660310889183498299)
              ·
                refine ⟨10227039990466333775247449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6818026660310889183498299 10227039990466333775247449)
                ·
                  refine ⟨7670279992849750331435587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10227039990466333775247449 7670279992849750331435587)
                  ·
                    refine ⟨11505419989274625497153381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7670279992849750331435587 11505419989274625497153381)
                    ·
                      refine ⟨2157266247988992280716259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11505419989274625497153381 2157266247988992280716259)
                      ·
                        rfl

theorem cell23_4201261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_4201261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201261 prefixEnd_4201261 := by exact prefixLift 4201261
  have htrace : WordTrace (prefixWord ++ tailWord_4201261) baseStart_4201261 baseEnd_4201261 := by
    simpa [prefixWord, tailWord_4201261, baseEnd_4201261] using wordTrace_append hprefix tailTrace_4201261
  have hstable : (prefixWord ++ tailWord_4201261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201261).length < 2 ^ (prefixWord ++ tailWord_4201261).sum := by decide
  have hdescent : baseEnd_4201261 < baseStart_4201261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201284 : List Nat := [2, 3, 4, 2, 1, 2, 1, 2, 6]
def baseStart_4201284 : Nat := 118140960795 + 4201284 * 2 ^ 59
def prefixEnd_4201284 : Nat := 4983230072969 + 3 ^ 40 * 4201284 * 2
def baseEnd_4201284 : Nat := 239697562004893965636517

theorem tailTrace_4201284 : CollatzResearch.WordTrace tailWord_4201284 prefixEnd_4201284 239697562004893965636517 := by
  unfold tailWord_4201284
  simp only [CollatzResearch.WordTrace]
  refine ⟨76616708055736532513725453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102155610740982043351633937 76616708055736532513725453)
  ·
    refine ⟨28731265520901199692647045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76616708055736532513725453 28731265520901199692647045)
    ·
      refine ⟨5387112285168974942371321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28731265520901199692647045 5387112285168974942371321)
      ·
        refine ⟨4040334213876731206778491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5387112285168974942371321 4040334213876731206778491)
        ·
          refine ⟨6060501320815096810167737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4040334213876731206778491 6060501320815096810167737)
          ·
            refine ⟨4545375990611322607625803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6060501320815096810167737 4545375990611322607625803)
            ·
              refine ⟨6818063985916983911438705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4545375990611322607625803 6818063985916983911438705)
              ·
                refine ⟨5113547989437737933579029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6818063985916983911438705 5113547989437737933579029)
                ·
                  refine ⟨239697562004893965636517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5113547989437737933579029 239697562004893965636517)
                  ·
                    rfl

theorem cell23_4201284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 6].length) (baseStart_4201284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201284 prefixEnd_4201284 := by exact prefixLift 4201284
  have htrace : WordTrace (prefixWord ++ tailWord_4201284) baseStart_4201284 baseEnd_4201284 := by
    simpa [prefixWord, tailWord_4201284, baseEnd_4201284] using wordTrace_append hprefix tailTrace_4201284
  have hstable : (prefixWord ++ tailWord_4201284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201284).length < 2 ^ (prefixWord ++ tailWord_4201284).sum := by decide
  have hdescent : baseEnd_4201284 < baseStart_4201284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201303 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 5]
def baseStart_4201303 : Nat := 118140960795 + 4201303 * 2 ^ 59
def prefixEnd_4201303 : Nat := 4983230072969 + 3 ^ 40 * 4201303 * 2
def baseEnd_4201303 : Nat := 2157287814176481116391065

theorem tailTrace_4201303 : CollatzResearch.WordTrace tailWord_4201303 prefixEnd_4201303 2157287814176481116391065 := by
  unfold tailWord_4201303
  simp only [CollatzResearch.WordTrace]
  refine ⟨153234109098404231272392563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102156072732269487514928375 153234109098404231272392563)
  ·
    refine ⟨229851163647606346908588845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153234109098404231272392563 229851163647606346908588845)
    ·
      refine ⟨86194186367852380090720817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229851163647606346908588845 86194186367852380090720817)
      ·
        refine ⟨64645639775889285068040613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86194186367852380090720817 64645639775889285068040613)
        ·
          refine ⟨12121057457979240950257615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64645639775889285068040613 12121057457979240950257615)
          ·
            refine ⟨18181586186968861425386423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12121057457979240950257615 18181586186968861425386423)
            ·
              refine ⟨27272379280453292138079635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18181586186968861425386423 27272379280453292138079635)
              ·
                refine ⟨40908568920679938207119453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27272379280453292138079635 40908568920679938207119453)
                ·
                  refine ⟨15340713345254976827669795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40908568920679938207119453 15340713345254976827669795)
                  ·
                    refine ⟨23011070017882465241504693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15340713345254976827669795 23011070017882465241504693)
                    ·
                      refine ⟨2157287814176481116391065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23011070017882465241504693 2157287814176481116391065)
                      ·
                        rfl

theorem cell23_4201303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_4201303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201303 prefixEnd_4201303 := by exact prefixLift 4201303
  have htrace : WordTrace (prefixWord ++ tailWord_4201303) baseStart_4201303 baseEnd_4201303 := by
    simpa [prefixWord, tailWord_4201303, baseEnd_4201303] using wordTrace_append hprefix tailTrace_4201303
  have hstable : (prefixWord ++ tailWord_4201303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201303).length < 2 ^ (prefixWord ++ tailWord_4201303).sum := by decide
  have hdescent : baseEnd_4201303 < baseStart_4201303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201313 : List Nat := [1, 2, 3, 1, 1, 1, 2, 5, 1, 2, 4]
def baseStart_4201313 : Nat := 118140960795 + 4201313 * 2 ^ 59
def prefixEnd_4201313 : Nat := 4983230072969 + 3 ^ 40 * 4201313 * 2
def baseEnd_4201313 : Nat := 2157292948983026077266019

theorem tailTrace_4201313 : CollatzResearch.WordTrace tailWord_4201313 prefixEnd_4201313 2157292948983026077266019 := by
  unfold tailWord_4201313
  simp only [CollatzResearch.WordTrace]
  refine ⟨153234473828368002980256593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102156315885578668653504395 153234473828368002980256593)
  ·
    refine ⟨114925855371276002235192445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153234473828368002980256593 114925855371276002235192445)
    ·
      refine ⟨43097195764228500838197167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114925855371276002235192445 43097195764228500838197167)
      ·
        refine ⟨64645793646342751257295751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43097195764228500838197167 64645793646342751257295751)
        ·
          refine ⟨96968690469514126885943627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64645793646342751257295751 96968690469514126885943627)
          ·
            refine ⟨145453035704271190328915441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96968690469514126885943627 145453035704271190328915441)
            ·
              refine ⟨109089776778203392746686581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145453035704271190328915441 109089776778203392746686581)
              ·
                refine ⟨10227166572956568070001867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109089776778203392746686581 10227166572956568070001867)
                ·
                  refine ⟨15340749859434852105002801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10227166572956568070001867 15340749859434852105002801)
                  ·
                    refine ⟨11505562394576139078752101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15340749859434852105002801 11505562394576139078752101)
                    ·
                      refine ⟨2157292948983026077266019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11505562394576139078752101 2157292948983026077266019)
                      ·
                        rfl

theorem cell23_4201313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_4201313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201313 prefixEnd_4201313 := by exact prefixLift 4201313
  have htrace : WordTrace (prefixWord ++ tailWord_4201313) baseStart_4201313 baseEnd_4201313 := by
    simpa [prefixWord, tailWord_4201313, baseEnd_4201313] using wordTrace_append hprefix tailTrace_4201313
  have hstable : (prefixWord ++ tailWord_4201313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201313).length < 2 ^ (prefixWord ++ tailWord_4201313).sum := by decide
  have hdescent : baseEnd_4201313 < baseStart_4201313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201317 : List Nat := [1, 3, 1, 3, 1, 1, 4, 2, 3, 2, 2]
def baseStart_4201317 : Nat := 118140960795 + 4201317 * 2 ^ 59
def prefixEnd_4201317 : Nat := 4983230072969 + 3 ^ 40 * 4201317 * 2
def baseEnd_4201317 : Nat := 2157295002905644061616001

theorem tailTrace_4201317 : CollatzResearch.WordTrace tailWord_4201317 prefixEnd_4201317 2157295002905644061616001 := by
  unfold tailWord_4201317
  simp only [CollatzResearch.WordTrace]
  refine ⟨153234619720353511663402205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102156413146902341108934803 153234619720353511663402205)
  ·
    refine ⟨57462982395132566873775827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153234619720353511663402205 57462982395132566873775827)
    ·
      refine ⟨86194473592698850310663741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57462982395132566873775827 86194473592698850310663741)
      ·
        refine ⟨32322927597262068866498903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86194473592698850310663741 32322927597262068866498903)
        ·
          refine ⟨48484391395893103299748355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32322927597262068866498903 48484391395893103299748355)
          ·
            refine ⟨72726587093839654949622533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48484391395893103299748355 72726587093839654949622533)
            ·
              refine ⟨13636235080094935303054225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72726587093839654949622533 13636235080094935303054225)
              ·
                refine ⟨10227176310071201477290669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13636235080094935303054225 10227176310071201477290669)
                ·
                  refine ⟨3835191116276700553984001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10227176310071201477290669 3835191116276700553984001)
                  ·
                    refine ⟨2876393337207525415488001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3835191116276700553984001 2876393337207525415488001)
                    ·
                      refine ⟨2157295002905644061616001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2876393337207525415488001 2157295002905644061616001)
                      ·
                        rfl

theorem cell23_4201317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_4201317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201317 prefixEnd_4201317 := by exact prefixLift 4201317
  have htrace : WordTrace (prefixWord ++ tailWord_4201317) baseStart_4201317 baseEnd_4201317 := by
    simpa [prefixWord, tailWord_4201317, baseEnd_4201317] using wordTrace_append hprefix tailTrace_4201317
  have hstable : (prefixWord ++ tailWord_4201317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201317).length < 2 ^ (prefixWord ++ tailWord_4201317).sum := by decide
  have hdescent : baseEnd_4201317 < baseStart_4201317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201323 : List Nat := [1, 1, 1, 1, 2, 2, 8, 7]
def baseStart_4201323 : Nat := 118140960795 + 4201323 * 2 ^ 59
def prefixEnd_4201323 : Nat := 4983230072969 + 3 ^ 40 * 4201323 * 2
def baseEnd_4201323 : Nat := 79899929029243371782999

theorem tailTrace_4201323 : CollatzResearch.WordTrace tailWord_4201323 prefixEnd_4201323 79899929029243371782999 := by
  unfold tailWord_4201323
  simp only [CollatzResearch.WordTrace]
  refine ⟨153234838558331774688120623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102156559038887849792080415 153234838558331774688120623)
  ·
    refine ⟨229852257837497662032180935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153234838558331774688120623 229852257837497662032180935)
    ·
      refine ⟨344778386756246493048271403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229852257837497662032180935 344778386756246493048271403)
      ·
        refine ⟨517167580134369739572407105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344778386756246493048271403 517167580134369739572407105)
        ·
          refine ⟨387875685100777304679305329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 517167580134369739572407105 387875685100777304679305329)
          ·
            refine ⟨290906763825582978509478997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387875685100777304679305329 290906763825582978509478997)
            ·
              refine ⟨3409063638581050529407957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 290906763825582978509478997 3409063638581050529407957)
              ·
                refine ⟨79899929029243371782999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3409063638581050529407957 79899929029243371782999)
                ·
                  rfl

theorem cell23_4201323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 7].length) (baseStart_4201323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201323 prefixEnd_4201323 := by exact prefixLift 4201323
  have htrace : WordTrace (prefixWord ++ tailWord_4201323) baseStart_4201323 baseEnd_4201323 := by
    simpa [prefixWord, tailWord_4201323, baseEnd_4201323] using wordTrace_append hprefix tailTrace_4201323
  have hstable : (prefixWord ++ tailWord_4201323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201323).length < 2 ^ (prefixWord ++ tailWord_4201323).sum := by decide
  have hdescent : baseEnd_4201323 < baseStart_4201323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201367 : List Nat := [1, 1, 3, 3, 1, 2, 3, 3, 2, 1, 3]
def baseStart_4201367 : Nat := 118140960795 + 4201367 * 2 ^ 59
def prefixEnd_4201367 : Nat := 4983230072969 + 3 ^ 40 * 4201367 * 2
def baseEnd_4201367 : Nat := 2157320676938368865990771

theorem tailTrace_4201367 : CollatzResearch.WordTrace tailWord_4201367 prefixEnd_4201367 2157320676938368865990771 := by
  unfold tailWord_4201367
  simp only [CollatzResearch.WordTrace]
  refine ⟨153236443370172370202722355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102157628913448246801814903 153236443370172370202722355)
  ·
    refine ⟨229854665055258555304083533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153236443370172370202722355 229854665055258555304083533)
    ·
      refine ⟨86195499395721958239031325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229854665055258555304083533 86195499395721958239031325)
      ·
        refine ⟨32323312273395734339636747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86195499395721958239031325 32323312273395734339636747)
        ·
          refine ⟨48484968410093601509455121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32323312273395734339636747 48484968410093601509455121)
          ·
            refine ⟨36363726307570201132091341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48484968410093601509455121 36363726307570201132091341)
            ·
              refine ⟨13636397365338825424534253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36363726307570201132091341 13636397365338825424534253)
              ·
                refine ⟨5113649012002059534200345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13636397365338825424534253 5113649012002059534200345)
                ·
                  refine ⟨3835236759001544650650259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5113649012002059534200345 3835236759001544650650259)
                  ·
                    refine ⟨5752855138502316975975389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3835236759001544650650259 5752855138502316975975389)
                    ·
                      refine ⟨2157320676938368865990771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5752855138502316975975389 2157320676938368865990771)
                      ·
                        rfl

theorem cell23_4201367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_4201367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201367 prefixEnd_4201367 := by exact prefixLift 4201367
  have htrace : WordTrace (prefixWord ++ tailWord_4201367) baseStart_4201367 baseEnd_4201367 := by
    simpa [prefixWord, tailWord_4201367, baseEnd_4201367] using wordTrace_append hprefix tailTrace_4201367
  have hstable : (prefixWord ++ tailWord_4201367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201367).length < 2 ^ (prefixWord ++ tailWord_4201367).sum := by decide
  have hdescent : baseEnd_4201367 < baseStart_4201367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201420 : List Nat := [2, 2, 1, 4, 1, 1, 3, 1, 2, 2, 4]
def baseStart_4201420 : Nat := 118140960795 + 4201420 * 2 ^ 59
def prefixEnd_4201420 : Nat := 4983230072969 + 3 ^ 40 * 4201420 * 2
def baseEnd_4201420 : Nat := 2157347891413057158628027

theorem tailTrace_4201420 : CollatzResearch.WordTrace tailWord_4201420 prefixEnd_4201420 2157347891413057158628027 := by
  unfold tailWord_4201420
  simp only [CollatzResearch.WordTrace]
  refine ⟨76619188219490180127200857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102158917625986906836267809 76619188219490180127200857)
  ·
    refine ⟨57464391164617635095400643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76619188219490180127200857 57464391164617635095400643)
    ·
      refine ⟨86196586746926452643100965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57464391164617635095400643 86196586746926452643100965)
      ·
        refine ⟨16161860015048709870581431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86196586746926452643100965 16161860015048709870581431)
        ·
          refine ⟨24242790022573064805872147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16161860015048709870581431 24242790022573064805872147)
          ·
            refine ⟨36364185033859597208808221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24242790022573064805872147 36364185033859597208808221)
            ·
              refine ⟨13636569387697348953303083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36364185033859597208808221 13636569387697348953303083)
              ·
                refine ⟨20454854081546023429954625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13636569387697348953303083 20454854081546023429954625)
                ·
                  refine ⟨15341140561159517572465969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20454854081546023429954625 15341140561159517572465969)
                  ·
                    refine ⟨11505855420869638179349477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15341140561159517572465969 11505855420869638179349477)
                    ·
                      refine ⟨2157347891413057158628027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11505855420869638179349477 2157347891413057158628027)
                      ·
                        rfl

theorem cell23_4201420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_4201420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201420 prefixEnd_4201420 := by exact prefixLift 4201420
  have htrace : WordTrace (prefixWord ++ tailWord_4201420) baseStart_4201420 baseEnd_4201420 := by
    simpa [prefixWord, tailWord_4201420, baseEnd_4201420] using wordTrace_append hprefix tailTrace_4201420
  have hstable : (prefixWord ++ tailWord_4201420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201420).length < 2 ^ (prefixWord ++ tailWord_4201420).sum := by decide
  have hdescent : baseEnd_4201420 < baseStart_4201420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201445 : List Nat := [1, 3, 1, 6, 2, 1, 2, 1, 1, 3, 2]
def baseStart_4201445 : Nat := 118140960795 + 4201445 * 2 ^ 59
def prefixEnd_4201445 : Nat := 4983230072969 + 3 ^ 40 * 4201445 * 2
def baseEnd_4201445 : Nat := 2157360728429419560815413

theorem tailTrace_4201445 : CollatzResearch.WordTrace tailWord_4201445 prefixEnd_4201445 2157360728429419560815413 := by
  unfold tailWord_4201445
  simp only [CollatzResearch.WordTrace]
  refine ⟨153239288263889789524061789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102159525509259859682707859 153239288263889789524061789)
  ·
    refine ⟨57464733098958671071523171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153239288263889789524061789 57464733098958671071523171)
    ·
      refine ⟨86197099648438006607284757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57464733098958671071523171 86197099648438006607284757)
      ·
        refine ⟨4040489046020531559716473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 86197099648438006607284757 4040489046020531559716473)
        ·
          refine ⟨3030366784515398669787355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4040489046020531559716473 3030366784515398669787355)
          ·
            refine ⟨4545550176773098004681033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3030366784515398669787355 4545550176773098004681033)
            ·
              refine ⟨3409162632579823503510775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4545550176773098004681033 3409162632579823503510775)
              ·
                refine ⟨5113743948869735255266163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3409162632579823503510775 5113743948869735255266163)
                ·
                  refine ⟨7670615923304602882899245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5113743948869735255266163 7670615923304602882899245)
                  ·
                    refine ⟨2876480971239226081087217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7670615923304602882899245 2876480971239226081087217)
                    ·
                      refine ⟨2157360728429419560815413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2876480971239226081087217 2157360728429419560815413)
                      ·
                        rfl

theorem cell23_4201445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_4201445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201445 prefixEnd_4201445 := by exact prefixLift 4201445
  have htrace : WordTrace (prefixWord ++ tailWord_4201445) baseStart_4201445 baseEnd_4201445 := by
    simpa [prefixWord, tailWord_4201445, baseEnd_4201445] using wordTrace_append hprefix tailTrace_4201445
  have hstable : (prefixWord ++ tailWord_4201445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201445).length < 2 ^ (prefixWord ++ tailWord_4201445).sum := by decide
  have hdescent : baseEnd_4201445 < baseStart_4201445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201447 : List Nat := [1, 1, 5, 2, 2, 1, 1, 5, 5]
def baseStart_4201447 : Nat := 118140960795 + 4201447 * 2 ^ 59
def prefixEnd_4201447 : Nat := 4983230072969 + 3 ^ 40 * 4201447 * 2
def baseEnd_4201447 : Nat := 239706861710080950332267

theorem tailTrace_4201447 : CollatzResearch.WordTrace tailWord_4201447 prefixEnd_4201447 239706861710080950332267 := by
  unfold tailWord_4201447
  simp only [CollatzResearch.WordTrace]
  refine ⟨153239361209882543865634595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102159574139921695910423063 153239361209882543865634595)
  ·
    refine ⟨229859041814823815798451893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153239361209882543865634595 229859041814823815798451893)
    ·
      refine ⟨21549285170139732731104865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 229859041814823815798451893 21549285170139732731104865)
      ·
        refine ⟨16161963877604799548328649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21549285170139732731104865 16161963877604799548328649)
        ·
          refine ⟨12121472908203599661246487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16161963877604799548328649 12121472908203599661246487)
          ·
            refine ⟨18182209362305399491869731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12121472908203599661246487 18182209362305399491869731)
            ·
              refine ⟨27273314043458099237804597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18182209362305399491869731 27273314043458099237804597)
              ·
                refine ⟨2556873191574196803544181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27273314043458099237804597 2556873191574196803544181)
                ·
                  refine ⟨239706861710080950332267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2556873191574196803544181 239706861710080950332267)
                  ·
                    rfl

theorem cell23_4201447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5, 5].length) (baseStart_4201447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201447 prefixEnd_4201447 := by exact prefixLift 4201447
  have htrace : WordTrace (prefixWord ++ tailWord_4201447) baseStart_4201447 baseEnd_4201447 := by
    simpa [prefixWord, tailWord_4201447, baseEnd_4201447] using wordTrace_append hprefix tailTrace_4201447
  have hstable : (prefixWord ++ tailWord_4201447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201447).length < 2 ^ (prefixWord ++ tailWord_4201447).sum := by decide
  have hdescent : baseEnd_4201447 < baseStart_4201447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201480 : List Nat := [2, 1, 3, 2, 1, 3, 1, 2, 1, 3, 4]
def baseStart_4201480 : Nat := 118140960795 + 4201480 * 2 ^ 59
def prefixEnd_4201480 : Nat := 4983230072969 + 3 ^ 40 * 4201480 * 2
def baseEnd_4201480 : Nat := 2157378700252326923877751

theorem tailTrace_4201480 : CollatzResearch.WordTrace tailWord_4201480 prefixEnd_4201480 2157378700252326923877751 := by
  unfold tailWord_4201480
  simp only [CollatzResearch.WordTrace]
  refine ⟨76620282409381495250792947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102160376545841993667723929 76620282409381495250792947)
  ·
    refine ⟨114930423614072242876189421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76620282409381495250792947 114930423614072242876189421)
    ·
      refine ⟨43098908855277091078571033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114930423614072242876189421 43098908855277091078571033)
      ·
        refine ⟨32324181641457818308928275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43098908855277091078571033 32324181641457818308928275)
        ·
          refine ⟨48486272462186727463392413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32324181641457818308928275 48486272462186727463392413)
          ·
            refine ⟨18182352173320022798772155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48486272462186727463392413 18182352173320022798772155)
            ·
              refine ⟨27273528259980034198158233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18182352173320022798772155 27273528259980034198158233)
              ·
                refine ⟨20455146194985025648618675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27273528259980034198158233 20455146194985025648618675)
                ·
                  refine ⟨30682719292477538472928013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20455146194985025648618675 30682719292477538472928013)
                  ·
                    refine ⟨11506019734679076927348005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30682719292477538472928013 11506019734679076927348005)
                    ·
                      refine ⟨2157378700252326923877751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11506019734679076927348005 2157378700252326923877751)
                      ·
                        rfl

theorem cell23_4201480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_4201480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201480 prefixEnd_4201480 := by exact prefixLift 4201480
  have htrace : WordTrace (prefixWord ++ tailWord_4201480) baseStart_4201480 baseEnd_4201480 := by
    simpa [prefixWord, tailWord_4201480, baseEnd_4201480] using wordTrace_append hprefix tailTrace_4201480
  have hstable : (prefixWord ++ tailWord_4201480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201480).length < 2 ^ (prefixWord ++ tailWord_4201480).sum := by decide
  have hdescent : baseEnd_4201480 < baseStart_4201480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201514 : List Nat := [3, 1, 4, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_4201514 : Nat := 118140960795 + 4201514 * 2 ^ 59
def prefixEnd_4201514 : Nat := 4983230072969 + 3 ^ 40 * 4201514 * 2
def baseEnd_4201514 : Nat := 2157396158594579790852595

theorem tailTrace_4201514 : CollatzResearch.WordTrace tailWord_4201514 prefixEnd_4201514 2157396158594579790852595 := by
  unfold tailWord_4201514
  simp only [CollatzResearch.WordTrace]
  refine ⟨38310451225159953577080899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102161203267093209538882397 38310451225159953577080899)
  ·
    refine ⟨57465676837739930365621349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38310451225159953577080899 57465676837739930365621349)
    ·
      refine ⟨10774814407076236943554003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57465676837739930365621349 10774814407076236943554003)
      ·
        refine ⟨16162221610614355415331005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10774814407076236943554003 16162221610614355415331005)
        ·
          refine ⟨6060833103980383280749127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16162221610614355415331005 6060833103980383280749127)
          ·
            refine ⟨9091249655970574921123691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6060833103980383280749127 9091249655970574921123691)
            ·
              refine ⟨13636874483955862381685537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9091249655970574921123691 13636874483955862381685537)
              ·
                refine ⟨10227655862966896786264153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13636874483955862381685537 10227655862966896786264153)
                ·
                  refine ⟨7670741897225172589698115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10227655862966896786264153 7670741897225172589698115)
                  ·
                    refine ⟨11506112845837758884547173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7670741897225172589698115 11506112845837758884547173)
                    ·
                      refine ⟨2157396158594579790852595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11506112845837758884547173 2157396158594579790852595)
                      ·
                        rfl

theorem cell23_4201514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_4201514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201514 prefixEnd_4201514 := by exact prefixLift 4201514
  have htrace : WordTrace (prefixWord ++ tailWord_4201514) baseStart_4201514 baseEnd_4201514 := by
    simpa [prefixWord, tailWord_4201514, baseEnd_4201514] using wordTrace_append hprefix tailTrace_4201514
  have hstable : (prefixWord ++ tailWord_4201514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201514).length < 2 ^ (prefixWord ++ tailWord_4201514).sum := by decide
  have hdescent : baseEnd_4201514 < baseStart_4201514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201520 : List Nat := [2, 1, 1, 1, 2, 4, 2, 4, 6]
def baseStart_4201520 : Nat := 118140960795 + 4201520 * 2 ^ 59
def prefixEnd_4201520 : Nat := 4983230072969 + 3 ^ 40 * 4201520 * 2
def baseEnd_4201520 : Nat := 239711026608722974153063

theorem tailTrace_4201520 : CollatzResearch.WordTrace tailWord_4201520 prefixEnd_4201520 239711026608722974153063 := by
  unfold tailWord_4201520
  simp only [CollatzResearch.WordTrace]
  refine ⟨76621011869309038666521007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102161349159078718222028009 76621011869309038666521007)
  ·
    refine ⟨114931517803963557999781511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76621011869309038666521007 114931517803963557999781511)
    ·
      refine ⟨172397276705945336999672267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114931517803963557999781511 172397276705945336999672267)
      ·
        refine ⟨258595915058918005499508401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172397276705945336999672267 258595915058918005499508401)
        ·
          refine ⟨193946936294188504124631301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258595915058918005499508401 193946936294188504124631301)
          ·
            refine ⟨36365050555160344523368369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193946936294188504124631301 36365050555160344523368369)
            ·
              refine ⟨27273787916370258392526277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36365050555160344523368369 27273787916370258392526277)
              ·
                refine ⟨5113835234319423448598677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27273787916370258392526277 5113835234319423448598677)
                ·
                  refine ⟨239711026608722974153063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5113835234319423448598677 239711026608722974153063)
                  ·
                    rfl

theorem cell23_4201520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 6].length) (baseStart_4201520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201520 prefixEnd_4201520 := by exact prefixLift 4201520
  have htrace : WordTrace (prefixWord ++ tailWord_4201520) baseStart_4201520 baseEnd_4201520 := by
    simpa [prefixWord, tailWord_4201520, baseEnd_4201520] using wordTrace_append hprefix tailTrace_4201520
  have hstable : (prefixWord ++ tailWord_4201520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201520).length < 2 ^ (prefixWord ++ tailWord_4201520).sum := by decide
  have hdescent : baseEnd_4201520 < baseStart_4201520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201580 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 3, 6]
def baseStart_4201580 : Nat := 118140960795 + 4201580 * 2 ^ 59
def prefixEnd_4201580 : Nat := 4983230072969 + 3 ^ 40 * 4201580 * 2
def baseEnd_4201580 : Nat := 719143349439258844209097

theorem tailTrace_4201580 : CollatzResearch.WordTrace tailWord_4201580 prefixEnd_4201580 719143349439258844209097 := by
  unfold tailWord_4201580
  simp only [CollatzResearch.WordTrace]
  refine ⟨76622106059200353790113097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102162808078933805053484129 76622106059200353790113097)
  ·
    refine ⟨57466579544400265342584823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76622106059200353790113097 57466579544400265342584823)
    ·
      refine ⟨86199869316600398013877235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57466579544400265342584823 86199869316600398013877235)
      ·
        refine ⟨129299803974900597020815853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86199869316600398013877235 129299803974900597020815853)
        ·
          refine ⟨48487426490587723882805945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129299803974900597020815853 48487426490587723882805945)
          ·
            refine ⟨36365569867940792912104459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48487426490587723882805945 36365569867940792912104459)
            ·
              refine ⟨54548354801911189368156689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36365569867940792912104459 54548354801911189368156689)
              ·
                refine ⟨40911266101433392026117517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54548354801911189368156689 40911266101433392026117517)
                ·
                  refine ⟨15341724788037522009794069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40911266101433392026117517 15341724788037522009794069)
                  ·
                    refine ⟨719143349439258844209097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15341724788037522009794069 719143349439258844209097)
                    ·
                      rfl

theorem cell23_4201580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 6].length) (baseStart_4201580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201580 prefixEnd_4201580 := by exact prefixLift 4201580
  have htrace : WordTrace (prefixWord ++ tailWord_4201580) baseStart_4201580 baseEnd_4201580 := by
    simpa [prefixWord, tailWord_4201580, baseEnd_4201580] using wordTrace_append hprefix tailTrace_4201580
  have hstable : (prefixWord ++ tailWord_4201580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201580).length < 2 ^ (prefixWord ++ tailWord_4201580).sum := by decide
  have hdescent : baseEnd_4201580 < baseStart_4201580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201597 : List Nat := [1, 4, 1, 1, 3, 1, 4, 1, 1, 6]
def baseStart_4201597 : Nat := 118140960795 + 4201597 * 2 ^ 59
def prefixEnd_4201597 : Nat := 4983230072969 + 3 ^ 40 * 4201597 * 2
def baseEnd_4201597 : Nat := 719146259162967655371571

theorem tailTrace_4201597 : CollatzResearch.WordTrace tailWord_4201597 prefixEnd_4201597 719146259162967655371571 := by
  unfold tailWord_4201597
  simp only [CollatzResearch.WordTrace]
  refine ⟨153244832159339119483595045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102163221439559412989063363 153244832159339119483595045)
  ·
    refine ⟨28733406029876084903174071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153244832159339119483595045 28733406029876084903174071)
    ·
      refine ⟨43100109044814127354761107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28733406029876084903174071 43100109044814127354761107)
      ·
        refine ⟨64650163567221191032141661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43100109044814127354761107 64650163567221191032141661)
        ·
          refine ⟨24243811337707946637053123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64650163567221191032141661 24243811337707946637053123)
          ·
            refine ⟨36365717006561919955579685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24243811337707946637053123 36365717006561919955579685)
            ·
              refine ⟨6818571938730359991671191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36365717006561919955579685 6818571938730359991671191)
              ·
                refine ⟨10227857908095539987506787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6818571938730359991671191 10227857908095539987506787)
                ·
                  refine ⟨15341786862143309981260181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10227857908095539987506787 15341786862143309981260181)
                  ·
                    refine ⟨719146259162967655371571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15341786862143309981260181 719146259162967655371571)
                    ·
                      rfl

theorem cell23_4201597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_4201597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201597 prefixEnd_4201597 := by exact prefixLift 4201597
  have htrace : WordTrace (prefixWord ++ tailWord_4201597) baseStart_4201597 baseEnd_4201597 := by
    simpa [prefixWord, tailWord_4201597, baseEnd_4201597] using wordTrace_append hprefix tailTrace_4201597
  have hstable : (prefixWord ++ tailWord_4201597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201597).length < 2 ^ (prefixWord ++ tailWord_4201597).sum := by decide
  have hdescent : baseEnd_4201597 < baseStart_4201597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201600 : List Nat := [2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 6]
def baseStart_4201600 : Nat := 118140960795 + 4201600 * 2 ^ 59
def prefixEnd_4201600 : Nat := 4983230072969 + 3 ^ 40 * 4201600 * 2
def baseEnd_4201600 : Nat := 2157440317930866454377199

theorem tailTrace_4201600 : CollatzResearch.WordTrace tailWord_4201600 prefixEnd_4201600 2157440317930866454377199 := by
  unfold tailWord_4201600
  simp only [CollatzResearch.WordTrace]
  refine ⟨76622470789164125497977127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102163294385552167330636169 76622470789164125497977127)
  ·
    refine ⟨114933706183746188246965691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76622470789164125497977127 114933706183746188246965691)
    ·
      refine ⟨172400559275619282370448537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114933706183746188246965691 172400559275619282370448537)
      ·
        refine ⟨129300419456714461777836403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172400559275619282370448537 129300419456714461777836403)
        ·
          refine ⟨193950629185071692666754605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129300419456714461777836403 193950629185071692666754605)
          ·
            refine ⟨72731485944401884750032977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193950629185071692666754605 72731485944401884750032977)
            ·
              refine ⟨54548614458301413562524733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72731485944401884750032977 54548614458301413562524733)
              ·
                refine ⟨20455730421863030085946775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54548614458301413562524733 20455730421863030085946775)
                ·
                  refine ⟨30683595632794545128920163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20455730421863030085946775 30683595632794545128920163)
                  ·
                    refine ⟨46025393449191817693380245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30683595632794545128920163 46025393449191817693380245)
                    ·
                      refine ⟨2157440317930866454377199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46025393449191817693380245 2157440317930866454377199)
                      ·
                        rfl

theorem cell23_4201600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_4201600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201600 prefixEnd_4201600 := by exact prefixLift 4201600
  have htrace : WordTrace (prefixWord ++ tailWord_4201600) baseStart_4201600 baseEnd_4201600 := by
    simpa [prefixWord, tailWord_4201600, baseEnd_4201600] using wordTrace_append hprefix tailTrace_4201600
  have hstable : (prefixWord ++ tailWord_4201600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201600).length < 2 ^ (prefixWord ++ tailWord_4201600).sum := by decide
  have hdescent : baseEnd_4201600 < baseStart_4201600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201608 : List Nat := [2, 1, 3, 4, 2, 2, 1, 1, 2, 3, 2]
def baseStart_4201608 : Nat := 118140960795 + 4201608 * 2 ^ 59
def prefixEnd_4201608 : Nat := 4983230072969 + 3 ^ 40 * 4201608 * 2
def baseEnd_4201608 : Nat := 2157444425776102423077163

theorem tailTrace_4201608 : CollatzResearch.WordTrace tailWord_4201608 prefixEnd_4201608 2157444425776102423077163 := by
  unfold tailWord_4201608
  simp only [CollatzResearch.WordTrace]
  refine ⟨76622616681149634181122739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102163488908199512241496985 76622616681149634181122739)
  ·
    refine ⟨114933925021724451271684109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76622616681149634181122739 114933925021724451271684109)
    ·
      refine ⟨43100221883146669226881541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114933925021724451271684109 43100221883146669226881541)
      ·
        refine ⟨8081291603090000480040289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43100221883146669226881541 8081291603090000480040289)
        ·
          refine ⟨6060968702317500360030217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8081291603090000480040289 6060968702317500360030217)
          ·
            refine ⟨4545726526738125270022663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6060968702317500360030217 4545726526738125270022663)
            ·
              refine ⟨6818589790107187905033995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4545726526738125270022663 6818589790107187905033995)
              ·
                refine ⟨10227884685160781857550993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6818589790107187905033995 10227884685160781857550993)
                ·
                  refine ⟨7670913513870586393163245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10227884685160781857550993 7670913513870586393163245)
                  ·
                    refine ⟨2876592567701469897436217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7670913513870586393163245 2876592567701469897436217)
                    ·
                      refine ⟨2157444425776102423077163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2876592567701469897436217 2157444425776102423077163)
                      ·
                        rfl

theorem cell23_4201608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_4201608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201608 prefixEnd_4201608 := by exact prefixLift 4201608
  have htrace : WordTrace (prefixWord ++ tailWord_4201608) baseStart_4201608 baseEnd_4201608 := by
    simpa [prefixWord, tailWord_4201608, baseEnd_4201608] using wordTrace_append hprefix tailTrace_4201608
  have hstable : (prefixWord ++ tailWord_4201608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201608).length < 2 ^ (prefixWord ++ tailWord_4201608).sum := by decide
  have hdescent : baseEnd_4201608 < baseStart_4201608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201758 : List Nat := [4, 3, 2, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_4201758 : Nat := 118140960795 + 4201758 * 2 ^ 59
def prefixEnd_4201758 : Nat := 4983230072969 + 3 ^ 40 * 4201758 * 2
def baseEnd_4201758 : Nat := 2157521447874276836201473

theorem tailTrace_4201758 : CollatzResearch.WordTrace tailWord_4201758 prefixEnd_4201758 2157521447874276836201473 := by
  unfold tailWord_4201758
  simp only [CollatzResearch.WordTrace]
  refine ⟨19156338038969480497525741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102167136207837229320137285 19156338038969480497525741)
  ·
    refine ⟨7183626764613555186572153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19156338038969480497525741 7183626764613555186572153)
    ·
      refine ⟨5387720073460166389929115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7183626764613555186572153 5387720073460166389929115)
      ·
        refine ⟨8081580110190249584893673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5387720073460166389929115 8081580110190249584893673)
        ·
          refine ⟨6061185082642687188670255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8081580110190249584893673 6061185082642687188670255)
          ·
            refine ⟨9091777623964030783005383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6061185082642687188670255 9091777623964030783005383)
            ·
              refine ⟨13637666435946046174508075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9091777623964030783005383 13637666435946046174508075)
              ·
                refine ⟨20456499653919069261762113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13637666435946046174508075 20456499653919069261762113)
                ·
                  refine ⟨15342374740439301946321585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20456499653919069261762113 15342374740439301946321585)
                  ·
                    refine ⟨11506781055329476459741189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15342374740439301946321585 11506781055329476459741189)
                    ·
                      refine ⟨2157521447874276836201473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11506781055329476459741189 2157521447874276836201473)
                      ·
                        rfl

theorem cell23_4201758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_4201758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201758 prefixEnd_4201758 := by exact prefixLift 4201758
  have htrace : WordTrace (prefixWord ++ tailWord_4201758) baseStart_4201758 baseEnd_4201758 := by
    simpa [prefixWord, tailWord_4201758, baseEnd_4201758] using wordTrace_append hprefix tailTrace_4201758
  have hstable : (prefixWord ++ tailWord_4201758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201758).length < 2 ^ (prefixWord ++ tailWord_4201758).sum := by decide
  have hdescent : baseEnd_4201758 < baseStart_4201758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201781 : List Nat := [1, 3, 3, 1, 2, 4, 1, 1, 2, 5]
def baseStart_4201781 : Nat := 118140960795 + 4201781 * 2 ^ 59
def prefixEnd_4201781 : Nat := 4983230072969 + 3 ^ 40 * 4201781 * 2
def baseEnd_4201781 : Nat := 719177752643110082071289

theorem tailTrace_4201781 : CollatzResearch.WordTrace tailWord_4201781 prefixEnd_4201781 719177752643110082071289 := by
  unfold tailWord_4201781
  simp only [CollatzResearch.WordTrace]
  refine ⟨153251543190672518908293197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102167695460448345938862131 153251543190672518908293197)
  ·
    refine ⟨57469328696502194590609949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153251543190672518908293197 57469328696502194590609949)
    ·
      refine ⟨21550998261188322971478731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57469328696502194590609949 21550998261188322971478731)
      ·
        refine ⟨32326497391782484457218097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21550998261188322971478731 32326497391782484457218097)
        ·
          refine ⟨24244873043836863342913573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32326497391782484457218097 24244873043836863342913573)
          ·
            refine ⟨4545913695719411876796295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24244873043836863342913573 4545913695719411876796295)
            ·
              refine ⟨6818870543579117815194443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4545913695719411876796295 6818870543579117815194443)
              ·
                refine ⟨10228305815368676722791665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6818870543579117815194443 10228305815368676722791665)
                ·
                  refine ⟨7671229361526507542093749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10228305815368676722791665 7671229361526507542093749)
                  ·
                    refine ⟨719177752643110082071289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7671229361526507542093749 719177752643110082071289)
                    ·
                      rfl

theorem cell23_4201781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_4201781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201781 prefixEnd_4201781 := by exact prefixLift 4201781
  have htrace : WordTrace (prefixWord ++ tailWord_4201781) baseStart_4201781 baseEnd_4201781 := by
    simpa [prefixWord, tailWord_4201781, baseEnd_4201781] using wordTrace_append hprefix tailTrace_4201781
  have hstable : (prefixWord ++ tailWord_4201781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201781).length < 2 ^ (prefixWord ++ tailWord_4201781).sum := by decide
  have hdescent : baseEnd_4201781 < baseStart_4201781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201784 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 3, 6, 2]
def baseStart_4201784 : Nat := 118140960795 + 4201784 * 2 ^ 59
def prefixEnd_4201784 : Nat := 4983230072969 + 3 ^ 40 * 4201784 * 2
def baseEnd_4201784 : Nat := 2157534798371293734476353

theorem tailTrace_4201784 : CollatzResearch.WordTrace tailWord_4201784 prefixEnd_4201784 2157534798371293734476353 := by
  unfold tailWord_4201784
  simp only [CollatzResearch.WordTrace]
  refine ⟨76625826304830825210326203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102167768406441100280434937 76625826304830825210326203)
  ·
    refine ⟨114938739457246237815489305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76625826304830825210326203 114938739457246237815489305)
    ·
      refine ⟨86204054592934678361616979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114938739457246237815489305 86204054592934678361616979)
      ·
        refine ⟨129306081889402017542425469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86204054592934678361616979 129306081889402017542425469)
        ·
          refine ⟨48489780708525756578409551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129306081889402017542425469 48489780708525756578409551)
          ·
            refine ⟨72734671062788634867614327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48489780708525756578409551 72734671062788634867614327)
            ·
              refine ⟨109102006594182952301421491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72734671062788634867614327 109102006594182952301421491)
              ·
                refine ⟨163653009891274428452132237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109102006594182952301421491 163653009891274428452132237)
                ·
                  refine ⟨61369878709227910669549589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163653009891274428452132237 61369878709227910669549589)
                  ·
                    refine ⟨2876713064495058312635137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61369878709227910669549589 2876713064495058312635137)
                    ·
                      refine ⟨2157534798371293734476353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2876713064495058312635137 2157534798371293734476353)
                      ·
                        rfl

theorem cell23_4201784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 6, 2].length) (baseStart_4201784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201784 prefixEnd_4201784 := by exact prefixLift 4201784
  have htrace : WordTrace (prefixWord ++ tailWord_4201784) baseStart_4201784 baseEnd_4201784 := by
    simpa [prefixWord, tailWord_4201784, baseEnd_4201784] using wordTrace_append hprefix tailTrace_4201784
  have hstable : (prefixWord ++ tailWord_4201784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201784).length < 2 ^ (prefixWord ++ tailWord_4201784).sum := by decide
  have hdescent : baseEnd_4201784 < baseStart_4201784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201797 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 1, 6, 4]
def baseStart_4201797 : Nat := 118140960795 + 4201797 * 2 ^ 59
def prefixEnd_4201797 : Nat := 4983230072969 + 3 ^ 40 * 4201797 * 2
def baseEnd_4201797 : Nat := 2157541473619802183613793

theorem tailTrace_4201797 : CollatzResearch.WordTrace tailWord_4201797 prefixEnd_4201797 2157541473619802183613793 := by
  unfold tailWord_4201797
  simp only [CollatzResearch.WordTrace]
  refine ⟨153252126758614553640875645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102168084505743035760583763 153252126758614553640875645)
  ·
    refine ⟨57469547534480457615328367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153252126758614553640875645 57469547534480457615328367)
    ·
      refine ⟨86204321301720686422992551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57469547534480457615328367 86204321301720686422992551)
      ·
        refine ⟨129306481952581029634488827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86204321301720686422992551 129306481952581029634488827)
        ·
          refine ⟨193959722928871544451733241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129306481952581029634488827 193959722928871544451733241)
          ·
            refine ⟨145469792196653658338799931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193959722928871544451733241 145469792196653658338799931)
            ·
              refine ⟨218204688294980487508199897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145469792196653658338799931 218204688294980487508199897)
              ·
                refine ⟨163653516221235365631149923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218204688294980487508199897 163653516221235365631149923)
                ·
                  refine ⟨245480274331853048446724885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163653516221235365631149923 245480274331853048446724885)
                  ·
                    refine ⟨11506887859305611645940229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 245480274331853048446724885 11506887859305611645940229)
                    ·
                      refine ⟨2157541473619802183613793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11506887859305611645940229 2157541473619802183613793)
                      ·
                        rfl

theorem cell23_4201797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_4201797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201797 prefixEnd_4201797 := by exact prefixLift 4201797
  have htrace : WordTrace (prefixWord ++ tailWord_4201797) baseStart_4201797 baseEnd_4201797 := by
    simpa [prefixWord, tailWord_4201797, baseEnd_4201797] using wordTrace_append hprefix tailTrace_4201797
  have hstable : (prefixWord ++ tailWord_4201797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201797).length < 2 ^ (prefixWord ++ tailWord_4201797).sum := by decide
  have hdescent : baseEnd_4201797 < baseStart_4201797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201811 : List Nat := [1, 1, 1, 2, 1, 1, 5, 6, 1, 4]
def baseStart_4201811 : Nat := 118140960795 + 4201811 * 2 ^ 59
def prefixEnd_4201811 : Nat := 4983230072969 + 3 ^ 40 * 4201811 * 2
def baseEnd_4201811 : Nat := 719182887449655042946243

theorem tailTrace_4201811 : CollatzResearch.WordTrace tailWord_4201811 prefixEnd_4201811 719182887449655042946243 := by
  unfold tailWord_4201811
  simp only [CollatzResearch.WordTrace]
  refine ⟨153252637380563834031885287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102168424920375889354590191 153252637380563834031885287)
  ·
    refine ⟨229878956070845751047827931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153252637380563834031885287 229878956070845751047827931)
    ·
      refine ⟨344818434106268626571741897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229878956070845751047827931 344818434106268626571741897)
      ·
        refine ⟨258613825579701469928806423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344818434106268626571741897 258613825579701469928806423)
        ·
          refine ⟨387920738369552204893209635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258613825579701469928806423 387920738369552204893209635)
          ·
            refine ⟨581881107554328307339814453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387920738369552204893209635 581881107554328307339814453)
            ·
              refine ⟨54551353833218278813107605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 581881107554328307339814453 54551353833218278813107605)
              ·
                refine ⟨2557094710932106819364419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54551353833218278813107605 2557094710932106819364419)
                ·
                  refine ⟨3835642066398160229046629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2557094710932106819364419 3835642066398160229046629)
                  ·
                    refine ⟨719182887449655042946243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3835642066398160229046629 719182887449655042946243)
                    ·
                      rfl

theorem cell23_4201811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6, 1, 4].length) (baseStart_4201811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201811 prefixEnd_4201811 := by exact prefixLift 4201811
  have htrace : WordTrace (prefixWord ++ tailWord_4201811) baseStart_4201811 baseEnd_4201811 := by
    simpa [prefixWord, tailWord_4201811, baseEnd_4201811] using wordTrace_append hprefix tailTrace_4201811
  have hstable : (prefixWord ++ tailWord_4201811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201811).length < 2 ^ (prefixWord ++ tailWord_4201811).sum := by decide
  have hdescent : baseEnd_4201811 < baseStart_4201811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201861 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 4, 3, 2]
def baseStart_4201861 : Nat := 118140960795 + 4201861 * 2 ^ 59
def prefixEnd_4201861 : Nat := 4983230072969 + 3 ^ 40 * 4201861 * 2
def baseEnd_4201861 : Nat := 2157574336381689933213499

theorem tailTrace_4201861 : CollatzResearch.WordTrace tailWord_4201861 prefixEnd_4201861 2157574336381689933213499 := by
  unfold tailWord_4201861
  simp only [CollatzResearch.WordTrace]
  refine ⟨153254461030382692571205437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102169640686921795047470291 153254461030382692571205437)
  ·
    refine ⟨57470422886393509714202039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153254461030382692571205437 57470422886393509714202039)
    ·
      refine ⟨86205634329590264571303059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57470422886393509714202039 86205634329590264571303059)
      ·
        refine ⟨129308451494385396856954589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86205634329590264571303059 129308451494385396856954589)
        ·
          refine ⟨48490669310394523821357971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129308451494385396856954589 48490669310394523821357971)
          ·
            refine ⟨72736003965591785732036957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48490669310394523821357971 72736003965591785732036957)
            ·
              refine ⟨27276001487096919649513859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72736003965591785732036957 27276001487096919649513859)
              ·
                refine ⟨40914002230645379474270789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27276001487096919649513859 40914002230645379474270789)
                ·
                  refine ⟨7671375418246008651425773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40914002230645379474270789 7671375418246008651425773)
                  ·
                    refine ⟨2876765781842253244284665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7671375418246008651425773 2876765781842253244284665)
                    ·
                      refine ⟨2157574336381689933213499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2876765781842253244284665 2157574336381689933213499)
                      ·
                        rfl

theorem cell23_4201861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 3, 2].length) (baseStart_4201861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201861 prefixEnd_4201861 := by exact prefixLift 4201861
  have htrace : WordTrace (prefixWord ++ tailWord_4201861) baseStart_4201861 baseEnd_4201861 := by
    simpa [prefixWord, tailWord_4201861, baseEnd_4201861] using wordTrace_append hprefix tailTrace_4201861
  have hstable : (prefixWord ++ tailWord_4201861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201861).length < 2 ^ (prefixWord ++ tailWord_4201861).sum := by decide
  have hdescent : baseEnd_4201861 < baseStart_4201861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201901 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 3, 6]
def baseStart_4201901 : Nat := 118140960795 + 4201901 * 2 ^ 59
def prefixEnd_4201901 : Nat := 4983230072969 + 3 ^ 40 * 4201901 * 2
def baseEnd_4201901 : Nat := 719198291869289925571105

theorem tailTrace_4201901 : CollatzResearch.WordTrace tailWord_4201901 prefixEnd_4201901 719198291869289925571105 := by
  unfold tailWord_4201901
  simp only [CollatzResearch.WordTrace]
  refine ⟨153255919950237779402661557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102170613300158519601774371 153255919950237779402661557)
  ·
    refine ⟨14367742495334791818999521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 153255919950237779402661557 14367742495334791818999521)
    ·
      refine ⟨10775806871501093864249641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14367742495334791818999521 10775806871501093864249641)
      ·
        refine ⟨8081855153625820398187231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10775806871501093864249641 8081855153625820398187231)
        ·
          refine ⟨12122782730438730597280847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8081855153625820398187231 12122782730438730597280847)
          ·
            refine ⟨18184174095658095895921271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12122782730438730597280847 18184174095658095895921271)
            ·
              refine ⟨27276261143487143843881907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18184174095658095895921271 27276261143487143843881907)
              ·
                refine ⟨40914391715230715765822861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27276261143487143843881907 40914391715230715765822861)
                ·
                  refine ⟨15342896893211518412183573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40914391715230715765822861 15342896893211518412183573)
                  ·
                    refine ⟨719198291869289925571105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15342896893211518412183573 719198291869289925571105)
                    ·
                      rfl

theorem cell23_4201901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_4201901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201901 prefixEnd_4201901 := by exact prefixLift 4201901
  have htrace : WordTrace (prefixWord ++ tailWord_4201901) baseStart_4201901 baseEnd_4201901 := by
    simpa [prefixWord, tailWord_4201901, baseEnd_4201901] using wordTrace_append hprefix tailTrace_4201901
  have hstable : (prefixWord ++ tailWord_4201901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201901).length < 2 ^ (prefixWord ++ tailWord_4201901).sum := by decide
  have hdescent : baseEnd_4201901 < baseStart_4201901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201934 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6]
def baseStart_4201934 : Nat := 118140960795 + 4201934 * 2 ^ 59
def prefixEnd_4201934 : Nat := 4983230072969 + 3 ^ 40 * 4201934 * 2
def baseEnd_4201934 : Nat := 2157611820469468147600663

theorem tailTrace_4201934 : CollatzResearch.WordTrace tailWord_4201934 prefixEnd_4201934 2157611820469468147600663 := by
  unfold tailWord_4201934
  simp only [CollatzResearch.WordTrace]
  refine ⟨19157140444889778254826607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102171415706078817359075237 19157140444889778254826607)
  ·
    refine ⟨28735710667334667382239911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19157140444889778254826607 28735710667334667382239911)
    ·
      refine ⟨43103566001002001073359867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28735710667334667382239911 43103566001002001073359867)
      ·
        refine ⟨64655349001503001610039801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43103566001002001073359867 64655349001503001610039801)
        ·
          refine ⟨48491511751127251207529851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64655349001503001610039801 48491511751127251207529851)
          ·
            refine ⟨72737267626690876811294777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48491511751127251207529851 72737267626690876811294777)
            ·
              refine ⟨54552950720018157608471083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72737267626690876811294777 54552950720018157608471083)
              ·
                refine ⟨81829426080027236412706625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54552950720018157608471083 81829426080027236412706625)
                ·
                  refine ⟨61372069560020427309529969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81829426080027236412706625 61372069560020427309529969)
                  ·
                    refine ⟨46029052170015320482147477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61372069560020427309529969 46029052170015320482147477)
                    ·
                      refine ⟨2157611820469468147600663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46029052170015320482147477 2157611820469468147600663)
                      ·
                        rfl

theorem cell23_4201934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_4201934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201934 prefixEnd_4201934 := by exact prefixLift 4201934
  have htrace : WordTrace (prefixWord ++ tailWord_4201934) baseStart_4201934 baseEnd_4201934 := by
    simpa [prefixWord, tailWord_4201934, baseEnd_4201934] using wordTrace_append hprefix tailTrace_4201934
  have hstable : (prefixWord ++ tailWord_4201934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201934).length < 2 ^ (prefixWord ++ tailWord_4201934).sum := by decide
  have hdescent : baseEnd_4201934 < baseStart_4201934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201942 : List Nat := [5, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2]
def baseStart_4201942 : Nat := 118140960795 + 4201942 * 2 ^ 59
def prefixEnd_4201942 : Nat := 4983230072969 + 3 ^ 40 * 4201942 * 2
def baseEnd_4201942 : Nat := 2157615928314704116300627

theorem tailTrace_4201942 : CollatzResearch.WordTrace tailWord_4201942 prefixEnd_4201942 2157615928314704116300627 := by
  unfold tailWord_4201942
  simp only [CollatzResearch.WordTrace]
  refine ⟨9578588458943077712806505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102171610228726162269936053 9578588458943077712806505)
  ·
    refine ⟨7183941344207308284604879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9578588458943077712806505 7183941344207308284604879)
    ·
      refine ⟨10775912016310962426907319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7183941344207308284604879 10775912016310962426907319)
      ·
        refine ⟨16163868024466443640360979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10775912016310962426907319 16163868024466443640360979)
        ·
          refine ⟨24245802036699665460541469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16163868024466443640360979 24245802036699665460541469)
          ·
            refine ⟨9092175763762374547703051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24245802036699665460541469 9092175763762374547703051)
            ·
              refine ⟨13638263645643561821554577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9092175763762374547703051 13638263645643561821554577)
              ·
                refine ⟨10228697734232671366165933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13638263645643561821554577 10228697734232671366165933)
                ·
                  refine ⟨3835761650337251762312225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10228697734232671366165933 3835761650337251762312225)
                  ·
                    refine ⟨2876821237752938821734169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3835761650337251762312225 2876821237752938821734169)
                    ·
                      refine ⟨2157615928314704116300627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2876821237752938821734169 2157615928314704116300627)
                      ·
                        rfl

theorem cell23_4201942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_4201942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201942 prefixEnd_4201942 := by exact prefixLift 4201942
  have htrace : WordTrace (prefixWord ++ tailWord_4201942) baseStart_4201942 baseEnd_4201942 := by
    simpa [prefixWord, tailWord_4201942, baseEnd_4201942] using wordTrace_append hprefix tailTrace_4201942
  have hstable : (prefixWord ++ tailWord_4201942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201942).length < 2 ^ (prefixWord ++ tailWord_4201942).sum := by decide
  have hdescent : baseEnd_4201942 < baseStart_4201942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201962 : List Nat := [3, 1, 3, 1, 4, 2, 2, 1, 1, 2, 3]
def baseStart_4201962 : Nat := 118140960795 + 4201962 * 2 ^ 59
def prefixEnd_4201962 : Nat := 4983230072969 + 3 ^ 40 * 4201962 * 2
def baseEnd_4201962 : Nat := 2157626197927794038050535

theorem tailTrace_4201962 : CollatzResearch.WordTrace tailWord_4201962 prefixEnd_4201962 2157626197927794038050535 := by
  unfold tailWord_4201962
  simp only [CollatzResearch.WordTrace]
  refine ⟨38314536200754196705158035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102172096535344524547088093 38314536200754196705158035)
  ·
    refine ⟨57471804301131295057737053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38314536200754196705158035 57471804301131295057737053)
    ·
      refine ⟨21551926612924235646651395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57471804301131295057737053 21551926612924235646651395)
      ·
        refine ⟨32327889919386353469977093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21551926612924235646651395 32327889919386353469977093)
        ·
          refine ⟨6061479359884941275620705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32327889919386353469977093 6061479359884941275620705)
          ·
            refine ⟨4546109519913705956715529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6061479359884941275620705 4546109519913705956715529)
            ·
              refine ⟨3409582139935279467536647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4546109519913705956715529 3409582139935279467536647)
              ·
                refine ⟨5114373209902919201304971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3409582139935279467536647 5114373209902919201304971)
                ·
                  refine ⟨7671559814854378801957457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5114373209902919201304971 7671559814854378801957457)
                  ·
                    refine ⟨5753669861140784101468093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7671559814854378801957457 5753669861140784101468093)
                    ·
                      refine ⟨2157626197927794038050535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5753669861140784101468093 2157626197927794038050535)
                      ·
                        rfl

theorem cell23_4201962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_4201962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201962 prefixEnd_4201962 := by exact prefixLift 4201962
  have htrace : WordTrace (prefixWord ++ tailWord_4201962) baseStart_4201962 baseEnd_4201962 := by
    simpa [prefixWord, tailWord_4201962, baseEnd_4201962] using wordTrace_append hprefix tailTrace_4201962
  have hstable : (prefixWord ++ tailWord_4201962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201962).length < 2 ^ (prefixWord ++ tailWord_4201962).sum := by decide
  have hdescent : baseEnd_4201962 < baseStart_4201962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201964 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 4]
def baseStart_4201964 : Nat := 118140960795 + 4201964 * 2 ^ 59
def prefixEnd_4201964 : Nat := 4983230072969 + 3 ^ 40 * 4201964 * 2
def baseEnd_4201964 : Nat := 2157627224889103030225525

theorem tailTrace_4201964 : CollatzResearch.WordTrace tailWord_4201964 prefixEnd_4201964 2157627224889103030225525 := by
  unfold tailWord_4201964
  simp only [CollatzResearch.WordTrace]
  refine ⟨76629108874504770581102473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102172145166006360774803297 76629108874504770581102473)
  ·
    refine ⟨57471831655878577935826855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76629108874504770581102473 57471831655878577935826855)
    ·
      refine ⟨86207747483817866903740283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57471831655878577935826855 86207747483817866903740283)
      ·
        refine ⟨129311621225726800355610425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86207747483817866903740283 129311621225726800355610425)
        ·
          refine ⟨96983715919295100266707819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129311621225726800355610425 96983715919295100266707819)
          ·
            refine ⟨145475573878942650400061729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96983715919295100266707819 145475573878942650400061729)
            ·
              refine ⟨109106680409206987800046297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145475573878942650400061729 109106680409206987800046297)
              ·
                refine ⟨81830010306905240850034723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109106680409206987800046297 81830010306905240850034723)
                ·
                  refine ⟨122745015460357861275052085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81830010306905240850034723 122745015460357861275052085)
                  ·
                    refine ⟨11507345199408549494536133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 122745015460357861275052085 11507345199408549494536133)
                    ·
                      refine ⟨2157627224889103030225525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11507345199408549494536133 2157627224889103030225525)
                      ·
                        rfl

theorem cell23_4201964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_4201964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201964 prefixEnd_4201964 := by exact prefixLift 4201964
  have htrace : WordTrace (prefixWord ++ tailWord_4201964) baseStart_4201964 baseEnd_4201964 := by
    simpa [prefixWord, tailWord_4201964, baseEnd_4201964] using wordTrace_append hprefix tailTrace_4201964
  have hstable : (prefixWord ++ tailWord_4201964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201964).length < 2 ^ (prefixWord ++ tailWord_4201964).sum := by decide
  have hdescent : baseEnd_4201964 < baseStart_4201964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4201991 : List Nat := [1, 1, 4, 3, 2, 1, 2, 1, 2, 6]
def baseStart_4201991 : Nat := 118140960795 + 4201991 * 2 ^ 59
def prefixEnd_4201991 : Nat := 4983230072969 + 3 ^ 40 * 4201991 * 2
def baseEnd_4201991 : Nat := 719213696288924808195967

theorem tailTrace_4201991 : CollatzResearch.WordTrace tailWord_4201991 prefixEnd_4201991 719213696288924808195967 := by
  unfold tailWord_4201991
  simp only [CollatzResearch.WordTrace]
  refine ⟨153259202519911724773437827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102172801679941149848958551 153259202519911724773437827)
  ·
    refine ⟨229888803779867587160156741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153259202519911724773437827 229888803779867587160156741)
    ·
      refine ⟨43104150708725172592529389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229888803779867587160156741 43104150708725172592529389)
      ·
        refine ⟨16164056515771939722198521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43104150708725172592529389 16164056515771939722198521)
        ·
          refine ⟨12123042386828954791648891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16164056515771939722198521 12123042386828954791648891)
          ·
            refine ⟨18184563580243432187473337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12123042386828954791648891 18184563580243432187473337)
            ·
              refine ⟨13638422685182574140605003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18184563580243432187473337 13638422685182574140605003)
              ·
                refine ⟨20457634027773861210907505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13638422685182574140605003 20457634027773861210907505)
                ·
                  refine ⟨15343225520830395908180629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20457634027773861210907505 15343225520830395908180629)
                  ·
                    refine ⟨719213696288924808195967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15343225520830395908180629 719213696288924808195967)
                    ·
                      rfl

theorem cell23_4201991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_4201991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4201991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4201991 prefixEnd_4201991 := by exact prefixLift 4201991
  have htrace : WordTrace (prefixWord ++ tailWord_4201991) baseStart_4201991 baseEnd_4201991 := by
    simpa [prefixWord, tailWord_4201991, baseEnd_4201991] using wordTrace_append hprefix tailTrace_4201991
  have hstable : (prefixWord ++ tailWord_4201991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4201991).length < 2 ^ (prefixWord ++ tailWord_4201991).sum := by decide
  have hdescent : baseEnd_4201991 < baseStart_4201991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4201991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202068 : List Nat := [2, 4, 1, 1, 1, 2, 4, 1, 2, 5]
def baseStart_4202068 : Nat := 118140960795 + 4202068 * 2 ^ 59
def prefixEnd_4202068 : Nat := 4983230072969 + 3 ^ 40 * 4202068 * 2
def baseEnd_4202068 : Nat := 719226875625723541108349

theorem tailTrace_4202068 : CollatzResearch.WordTrace tailWord_4202068 prefixEnd_4202068 719226875625723541108349 := by
  unfold tailWord_4202068
  simp only [CollatzResearch.WordTrace]
  refine ⟨76631005470316383461995429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102174673960421844615993905 76631005470316383461995429)
  ·
    refine ⟨14368313525684321899124143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76631005470316383461995429 14368313525684321899124143)
    ·
      refine ⟨21552470288526482848686215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14368313525684321899124143 21552470288526482848686215)
      ·
        refine ⟨32328705432789724273029323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21552470288526482848686215 32328705432789724273029323)
        ·
          refine ⟨48493058149184586409543985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32328705432789724273029323 48493058149184586409543985)
          ·
            refine ⟨36369793611888439807157989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48493058149184586409543985 36369793611888439807157989)
            ·
              refine ⟨6819336302229082463842123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36369793611888439807157989 6819336302229082463842123)
              ·
                refine ⟨10229004453343623695763185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6819336302229082463842123 10229004453343623695763185)
                ·
                  refine ⟨7671753340007717771822389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10229004453343623695763185 7671753340007717771822389)
                  ·
                    refine ⟨719226875625723541108349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7671753340007717771822389 719226875625723541108349)
                    ·
                      rfl

theorem cell23_4202068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_4202068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202068 prefixEnd_4202068 := by exact prefixLift 4202068
  have htrace : WordTrace (prefixWord ++ tailWord_4202068) baseStart_4202068 baseEnd_4202068 := by
    simpa [prefixWord, tailWord_4202068, baseEnd_4202068] using wordTrace_append hprefix tailTrace_4202068
  have hstable : (prefixWord ++ tailWord_4202068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202068).length < 2 ^ (prefixWord ++ tailWord_4202068).sum := by decide
  have hdescent : baseEnd_4202068 < baseStart_4202068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202145 : List Nat := [1, 2, 3, 3, 2, 3, 1, 2, 6]
def baseStart_4202145 : Nat := 118140960795 + 4202145 * 2 ^ 59
def prefixEnd_4202145 : Nat := 4983230072969 + 3 ^ 40 * 4202145 * 2
def baseEnd_4202145 : Nat := 239746684987507424673577

theorem tailTrace_4202145 : CollatzResearch.WordTrace tailWord_4202145 prefixEnd_4202145 239746684987507424673577 := by
  unfold tailWord_4202145
  simp only [CollatzResearch.WordTrace]
  refine ⟨153264819361353809074543889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102176546240902539383029259 153264819361353809074543889)
  ·
    refine ⟨114948614521015356805907917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153264819361353809074543889 114948614521015356805907917)
    ·
      refine ⟨43105730445380758802215469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114948614521015356805907917 43105730445380758802215469)
      ·
        refine ⟨16164648917017784550830801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43105730445380758802215469 16164648917017784550830801)
        ·
          refine ⟨12123486687763338413123101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16164648917017784550830801 12123486687763338413123101)
          ·
            refine ⟨4546307507911251904921163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12123486687763338413123101 4546307507911251904921163)
            ·
              refine ⟨6819461261866877857381745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4546307507911251904921163 6819461261866877857381745)
              ·
                refine ⟨5114595946400158393036309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6819461261866877857381745 5114595946400158393036309)
                ·
                  refine ⟨239746684987507424673577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5114595946400158393036309 239746684987507424673577)
                  ·
                    rfl

theorem cell23_4202145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 6].length) (baseStart_4202145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202145 prefixEnd_4202145 := by exact prefixLift 4202145
  have htrace : WordTrace (prefixWord ++ tailWord_4202145) baseStart_4202145 baseEnd_4202145 := by
    simpa [prefixWord, tailWord_4202145, baseEnd_4202145] using wordTrace_append hprefix tailTrace_4202145
  have hstable : (prefixWord ++ tailWord_4202145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202145).length < 2 ^ (prefixWord ++ tailWord_4202145).sum := by decide
  have hdescent : baseEnd_4202145 < baseStart_4202145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202201 : List Nat := [1, 2, 1, 2, 3, 3, 11]
def baseStart_4202201 : Nat := 118140960795 + 4202201 * 2 ^ 59
def prefixEnd_4202201 : Nat := 4983230072969 + 3 ^ 40 * 4202201 * 2
def baseEnd_4202201 : Nat := 26638875553138501271135

theorem tailTrace_4202201 : CollatzResearch.WordTrace tailWord_4202201 prefixEnd_4202201 26638875553138501271135 := by
  unfold tailWord_4202201
  simp only [CollatzResearch.WordTrace]
  refine ⟨153266861849150930638582457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102177907899433953759054971 153266861849150930638582457)
  ·
    refine ⟨114950146386863197978936843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153266861849150930638582457 114950146386863197978936843)
    ·
      refine ⟨172425219580294796968405265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114950146386863197978936843 172425219580294796968405265)
      ·
        refine ⟨129318914685221097726303949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172425219580294796968405265 129318914685221097726303949)
        ·
          refine ⟨48494593006957911647363981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129318914685221097726303949 48494593006957911647363981)
          ·
            refine ⟨18185472377609216867761493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48494593006957911647363981 18185472377609216867761493)
            ·
              refine ⟨26638875553138501271135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 18185472377609216867761493 26638875553138501271135)
              ·
                rfl

theorem cell23_4202201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 11].length) (baseStart_4202201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202201 prefixEnd_4202201 := by exact prefixLift 4202201
  have htrace : WordTrace (prefixWord ++ tailWord_4202201) baseStart_4202201 baseEnd_4202201 := by
    simpa [prefixWord, tailWord_4202201, baseEnd_4202201] using wordTrace_append hprefix tailTrace_4202201
  have hstable : (prefixWord ++ tailWord_4202201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202201).length < 2 ^ (prefixWord ++ tailWord_4202201).sum := by decide
  have hdescent : baseEnd_4202201 < baseStart_4202201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202263 : List Nat := [1, 1, 3, 4, 2, 3, 2, 2, 1, 2, 2]
def baseStart_4202263 : Nat := 118140960795 + 4202263 * 2 ^ 59
def prefixEnd_4202263 : Nat := 4983230072969 + 3 ^ 40 * 4202263 * 2
def baseEnd_4202263 : Nat := 2157780755604797360386651

theorem tailTrace_4202263 : CollatzResearch.WordTrace tailWord_4202263 prefixEnd_4202263 2157780755604797360386651 := by
  unfold tailWord_4202263
  simp only [CollatzResearch.WordTrace]
  refine ⟨153269123174926315227339443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102179415449950876818226295 153269123174926315227339443)
  ·
    refine ⟨229903684762389472841009165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153269123174926315227339443 229903684762389472841009165)
    ·
      refine ⟨86213881785896052315378437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229903684762389472841009165 86213881785896052315378437)
      ·
        refine ⟨16165102834855509809133457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86213881785896052315378437 16165102834855509809133457)
        ·
          refine ⟨12123827126141632356850093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16165102834855509809133457 12123827126141632356850093)
          ·
            refine ⟨4546435172303112133818785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12123827126141632356850093 4546435172303112133818785)
            ·
              refine ⟨3409826379227334100364089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4546435172303112133818785 3409826379227334100364089)
              ·
                refine ⟨2557369784420500575273067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3409826379227334100364089 2557369784420500575273067)
                ·
                  refine ⟨3836054676630750862909601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2557369784420500575273067 3836054676630750862909601)
                  ·
                    refine ⟨2877041007473063147182201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3836054676630750862909601 2877041007473063147182201)
                    ·
                      refine ⟨2157780755604797360386651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2877041007473063147182201 2157780755604797360386651)
                      ·
                        rfl

theorem cell23_4202263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_4202263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202263 prefixEnd_4202263 := by exact prefixLift 4202263
  have htrace : WordTrace (prefixWord ++ tailWord_4202263) baseStart_4202263 baseEnd_4202263 := by
    simpa [prefixWord, tailWord_4202263, baseEnd_4202263] using wordTrace_append hprefix tailTrace_4202263
  have hstable : (prefixWord ++ tailWord_4202263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202263).length < 2 ^ (prefixWord ++ tailWord_4202263).sum := by decide
  have hdescent : baseEnd_4202263 < baseStart_4202263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202268 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_4202268 : Nat := 118140960795 + 4202268 * 2 ^ 59
def prefixEnd_4202268 : Nat := 4983230072969 + 3 ^ 40 * 4202268 * 2
def baseEnd_4202268 : Nat := 2157783323008069840824127

theorem tailTrace_4202268 : CollatzResearch.WordTrace tailWord_4202268 prefixEnd_4202268 2157783323008069840824127 := by
  unfold tailWord_4202268
  simp only [CollatzResearch.WordTrace]
  refine ⟨76634652769954100540635729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102179537026605467387514305 76634652769954100540635729)
  ·
    refine ⟨57475989577465575405476797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76634652769954100540635729 57475989577465575405476797)
    ·
      refine ⟨21553496091549590777053799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57475989577465575405476797 21553496091549590777053799)
      ·
        refine ⟨32330244137324386165580699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21553496091549590777053799 32330244137324386165580699)
        ·
          refine ⟨48495366205986579248371049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32330244137324386165580699 48495366205986579248371049)
          ·
            refine ⟨36371524654489934436278287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48495366205986579248371049 36371524654489934436278287)
            ·
              refine ⟨54557286981734901654417431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36371524654489934436278287 54557286981734901654417431)
              ·
                refine ⟨81835930472602352481626147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54557286981734901654417431 81835930472602352481626147)
                ·
                  refine ⟨122753895708903528722439221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81835930472602352481626147 122753895708903528722439221)
                  ·
                    refine ⟨11508177722709705817728677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 122753895708903528722439221 11508177722709705817728677)
                    ·
                      refine ⟨2157783323008069840824127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11508177722709705817728677 2157783323008069840824127)
                      ·
                        rfl

theorem cell23_4202268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_4202268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202268 prefixEnd_4202268 := by exact prefixLift 4202268
  have htrace : WordTrace (prefixWord ++ tailWord_4202268) baseStart_4202268 baseEnd_4202268 := by
    simpa [prefixWord, tailWord_4202268, baseEnd_4202268] using wordTrace_append hprefix tailTrace_4202268
  have hstable : (prefixWord ++ tailWord_4202268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202268).length < 2 ^ (prefixWord ++ tailWord_4202268).sum := by decide
  have hdescent : baseEnd_4202268 < baseStart_4202268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202325 : List Nat := [1, 3, 2, 2, 2, 3, 2, 1, 7]
def baseStart_4202325 : Nat := 118140960795 + 4202325 * 2 ^ 59
def prefixEnd_4202325 : Nat := 4983230072969 + 3 ^ 40 * 4202325 * 2
def baseEnd_4202325 : Nat := 239756954600597346423485

theorem tailTrace_4202325 : CollatzResearch.WordTrace tailWord_4202325 prefixEnd_4202325 239756954600597346423485 := by
  unfold tailWord_4202325
  simp only [CollatzResearch.WordTrace]
  refine ⟨153271384500701699816096429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102180923000467799877397619 153271384500701699816096429)
  ·
    refine ⟨57476769187763137431036161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153271384500701699816096429 57476769187763137431036161)
    ·
      refine ⟨43107576890822353073277121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57476769187763137431036161 43107576890822353073277121)
      ·
        refine ⟨32330682668116764804957841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43107576890822353073277121 32330682668116764804957841)
        ·
          refine ⟨24248012001087573603718381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32330682668116764804957841 24248012001087573603718381)
          ·
            refine ⟨9093004500407840101394393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24248012001087573603718381 9093004500407840101394393)
            ·
              refine ⟨6819753375305880076045795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9093004500407840101394393 6819753375305880076045795)
              ·
                refine ⟨10229630062958820114068693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6819753375305880076045795 10229630062958820114068693)
                ·
                  refine ⟨239756954600597346423485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10229630062958820114068693 239756954600597346423485)
                  ·
                    rfl

theorem cell23_4202325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 7].length) (baseStart_4202325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202325 prefixEnd_4202325 := by exact prefixLift 4202325
  have htrace : WordTrace (prefixWord ++ tailWord_4202325) baseStart_4202325 baseEnd_4202325 := by
    simpa [prefixWord, tailWord_4202325, baseEnd_4202325] using wordTrace_append hprefix tailTrace_4202325
  have hstable : (prefixWord ++ tailWord_4202325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202325).length < 2 ^ (prefixWord ++ tailWord_4202325).sum := by decide
  have hdescent : baseEnd_4202325 < baseStart_4202325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202335 : List Nat := [1, 1, 2, 3, 1, 4, 2, 1, 2, 3, 3]
def baseStart_4202335 : Nat := 118140960795 + 4202335 * 2 ^ 59
def prefixEnd_4202335 : Nat := 4983230072969 + 3 ^ 40 * 4202335 * 2
def baseEnd_4202335 : Nat := 2157817726211921078686319

theorem tailTrace_4202335 : CollatzResearch.WordTrace tailWord_4202335 prefixEnd_4202335 2157817726211921078686319 := by
  unfold tailWord_4202335
  simp only [CollatzResearch.WordTrace]
  refine ⟨153271749230665471523960459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102181166153776981015973639 153271749230665471523960459)
  ·
    refine ⟨229907623845998207285940689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153271749230665471523960459 229907623845998207285940689)
    ·
      refine ⟨172430717884498655464455517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229907623845998207285940689 172430717884498655464455517)
      ·
        refine ⟨64661519206686995799170819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172430717884498655464455517 64661519206686995799170819)
        ·
          refine ⟨96992278810030493698756229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64661519206686995799170819 96992278810030493698756229)
          ·
            refine ⟨18186052276880717568516793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96992278810030493698756229 18186052276880717568516793)
            ·
              refine ⟨13639539207660538176387595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18186052276880717568516793 13639539207660538176387595)
              ·
                refine ⟨20459308811490807264581393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13639539207660538176387595 20459308811490807264581393)
                ·
                  refine ⟨15344481608618105448436045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20459308811490807264581393 15344481608618105448436045)
                  ·
                    refine ⟨5754180603231789543163517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15344481608618105448436045 5754180603231789543163517)
                    ·
                      refine ⟨2157817726211921078686319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5754180603231789543163517 2157817726211921078686319)
                      ·
                        rfl

theorem cell23_4202335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_4202335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202335 prefixEnd_4202335 := by exact prefixLift 4202335
  have htrace : WordTrace (prefixWord ++ tailWord_4202335) baseStart_4202335 baseEnd_4202335 := by
    simpa [prefixWord, tailWord_4202335, baseEnd_4202335] using wordTrace_append hprefix tailTrace_4202335
  have hstable : (prefixWord ++ tailWord_4202335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202335).length < 2 ^ (prefixWord ++ tailWord_4202335).sum := by decide
  have hdescent : baseEnd_4202335 < baseStart_4202335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202336 : List Nat := [2, 1, 1, 3, 3, 3, 3, 1, 2, 2, 2]
def baseStart_4202336 : Nat := 118140960795 + 4202336 * 2 ^ 59
def prefixEnd_4202336 : Nat := 4983230072969 + 3 ^ 40 * 4202336 * 2
def baseEnd_4202336 : Nat := 2157818239692575574773815

theorem tailTrace_4202336 : CollatzResearch.WordTrace tailWord_4202336 prefixEnd_4202336 2157818239692575574773815 := by
  unfold tailWord_4202336
  simp only [CollatzResearch.WordTrace]
  refine ⟨76635892851830924347373431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102181190469107899129831241 76635892851830924347373431)
  ·
    refine ⟨114953839277746386521060147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76635892851830924347373431 114953839277746386521060147)
    ·
      refine ⟨172430758916619579781590221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114953839277746386521060147 172430758916619579781590221)
      ·
        refine ⟨64661534593732342418096333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172430758916619579781590221 64661534593732342418096333)
        ·
          refine ⟨24248075472649628406786125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64661534593732342418096333 24248075472649628406786125)
          ·
            refine ⟨9093028302243610652544797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24248075472649628406786125 9093028302243610652544797)
            ·
              refine ⟨3409885613341353994704299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9093028302243610652544797 3409885613341353994704299)
              ·
                refine ⟨5114828420012030992056449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3409885613341353994704299 5114828420012030992056449)
                ·
                  refine ⟨3836121315009023244042337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5114828420012030992056449 3836121315009023244042337)
                  ·
                    refine ⟨2877090986256767433031753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3836121315009023244042337 2877090986256767433031753)
                    ·
                      refine ⟨2157818239692575574773815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2877090986256767433031753 2157818239692575574773815)
                      ·
                        rfl

theorem cell23_4202336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 2, 2, 2].length) (baseStart_4202336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202336 prefixEnd_4202336 := by exact prefixLift 4202336
  have htrace : WordTrace (prefixWord ++ tailWord_4202336) baseStart_4202336 baseEnd_4202336 := by
    simpa [prefixWord, tailWord_4202336, baseEnd_4202336] using wordTrace_append hprefix tailTrace_4202336
  have hstable : (prefixWord ++ tailWord_4202336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202336).length < 2 ^ (prefixWord ++ tailWord_4202336).sum := by decide
  have hdescent : baseEnd_4202336 < baseStart_4202336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202345 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 2, 5, 2]
def baseStart_4202345 : Nat := 118140960795 + 4202345 * 2 ^ 59
def prefixEnd_4202345 : Nat := 4983230072969 + 3 ^ 40 * 4202345 * 2
def baseEnd_4202345 : Nat := 2157822861018466039561273

theorem tailTrace_4202345 : CollatzResearch.WordTrace tailWord_4202345 prefixEnd_4202345 2157822861018466039561273 := by
  unfold tailWord_4202345
  simp only [CollatzResearch.WordTrace]
  refine ⟨153272113960629243231824489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102181409307086162154549659 153272113960629243231824489)
  ·
    refine ⟨114954085470471932423868367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153272113960629243231824489 114954085470471932423868367)
    ·
      refine ⟨172431128205707898635802551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114954085470471932423868367 172431128205707898635802551)
      ·
        refine ⟨258646692308561847953703827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172431128205707898635802551 258646692308561847953703827)
        ·
          refine ⟨387970038462842771930555741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258646692308561847953703827 387970038462842771930555741)
          ·
            refine ⟨145488764423566039473958403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 387970038462842771930555741 145488764423566039473958403)
            ·
              refine ⟨218233146635349059210937605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145488764423566039473958403 218233146635349059210937605)
              ·
                refine ⟨40918714994127948602050801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 218233146635349059210937605 40918714994127948602050801)
                ·
                  refine ⟨30689036245595961451538101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40918714994127948602050801 30689036245595961451538101)
                  ·
                    refine ⟨2877097148024621386081697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30689036245595961451538101 2877097148024621386081697)
                    ·
                      refine ⟨2157822861018466039561273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2877097148024621386081697 2157822861018466039561273)
                      ·
                        rfl

theorem cell23_4202345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 5, 2].length) (baseStart_4202345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202345 prefixEnd_4202345 := by exact prefixLift 4202345
  have htrace : WordTrace (prefixWord ++ tailWord_4202345) baseStart_4202345 baseEnd_4202345 := by
    simpa [prefixWord, tailWord_4202345, baseEnd_4202345] using wordTrace_append hprefix tailTrace_4202345
  have hstable : (prefixWord ++ tailWord_4202345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202345).length < 2 ^ (prefixWord ++ tailWord_4202345).sum := by decide
  have hdescent : baseEnd_4202345 < baseStart_4202345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202460 : List Nat := [2, 2, 6, 1, 2, 1, 1, 1, 2, 1, 4]
def baseStart_4202460 : Nat := 118140960795 + 4202460 * 2 ^ 59
def prefixEnd_4202460 : Nat := 4983230072969 + 3 ^ 40 * 4202460 * 2
def baseEnd_4202460 : Nat := 2157881911293733089623245

theorem tailTrace_4202460 : CollatzResearch.WordTrace tailWord_4202460 prefixEnd_4202460 2157881911293733089623245 := by
  unfold tailWord_4202460
  simp only [CollatzResearch.WordTrace]
  refine ⟨76638154177606308936130417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102184205570141745248173889 76638154177606308936130417)
  ·
    refine ⟨57478615633204731702097813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76638154177606308936130417 57478615633204731702097813)
    ·
      refine ⟨2694310107806471798535835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 57478615633204731702097813 2694310107806471798535835)
      ·
        refine ⟨4041465161709707697803753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2694310107806471798535835 4041465161709707697803753)
        ·
          refine ⟨3031098871282280773352815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4041465161709707697803753 3031098871282280773352815)
          ·
            refine ⟨4546648306923421160029223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3031098871282280773352815 4546648306923421160029223)
            ·
              refine ⟨6819972460385131740043835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4546648306923421160029223 6819972460385131740043835)
              ·
                refine ⟨10229958690577697610065753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6819972460385131740043835 10229958690577697610065753)
                ·
                  refine ⟨7672469017933273207549315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10229958690577697610065753 7672469017933273207549315)
                  ·
                    refine ⟨11508703526899909811323973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7672469017933273207549315 11508703526899909811323973)
                    ·
                      refine ⟨2157881911293733089623245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11508703526899909811323973 2157881911293733089623245)
                      ·
                        rfl

theorem cell23_4202460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_4202460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202460 prefixEnd_4202460 := by exact prefixLift 4202460
  have htrace : WordTrace (prefixWord ++ tailWord_4202460) baseStart_4202460 baseEnd_4202460 := by
    simpa [prefixWord, tailWord_4202460, baseEnd_4202460] using wordTrace_append hprefix tailTrace_4202460
  have hstable : (prefixWord ++ tailWord_4202460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202460).length < 2 ^ (prefixWord ++ tailWord_4202460).sum := by decide
  have hdescent : baseEnd_4202460 < baseStart_4202460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202492 : List Nat := [2, 2, 2, 1, 2, 2, 3, 1, 4, 4]
def baseStart_4202492 : Nat := 118140960795 + 4202492 * 2 ^ 59
def prefixEnd_4202492 : Nat := 4983230072969 + 3 ^ 40 * 4202492 * 2
def baseEnd_4202492 : Nat := 719299447558225654807699

theorem tailTrace_4202492 : CollatzResearch.WordTrace tailWord_4202492 prefixEnd_4202492 719299447558225654807699 := by
  unfold tailWord_4202492
  simp only [CollatzResearch.WordTrace]
  refine ⟨76638737745548343668712865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102184983660731124891617153 76638737745548343668712865)
  ·
    refine ⟨57479053309161257751534649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76638737745548343668712865 57479053309161257751534649)
    ·
      refine ⟨43109289981870943313650987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57479053309161257751534649 43109289981870943313650987)
      ·
        refine ⟨64663934972806414970476481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43109289981870943313650987 64663934972806414970476481)
        ·
          refine ⟨48497951229604811227857361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64663934972806414970476481 48497951229604811227857361)
          ·
            refine ⟨36373463422203608420893021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48497951229604811227857361 36373463422203608420893021)
            ·
              refine ⟨13640048783326353157834883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36373463422203608420893021 13640048783326353157834883)
              ·
                refine ⟨20460073174989529736752325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13640048783326353157834883 20460073174989529736752325)
                ·
                  refine ⟨3836263720310536825641061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20460073174989529736752325 3836263720310536825641061)
                  ·
                    refine ⟨719299447558225654807699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3836263720310536825641061 719299447558225654807699)
                    ·
                      rfl

theorem cell23_4202492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_4202492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202492 prefixEnd_4202492 := by exact prefixLift 4202492
  have htrace : WordTrace (prefixWord ++ tailWord_4202492) baseStart_4202492 baseEnd_4202492 := by
    simpa [prefixWord, tailWord_4202492, baseEnd_4202492] using wordTrace_append hprefix tailTrace_4202492
  have hstable : (prefixWord ++ tailWord_4202492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202492).length < 2 ^ (prefixWord ++ tailWord_4202492).sum := by decide
  have hdescent : baseEnd_4202492 < baseStart_4202492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202495 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 4]
def baseStart_4202495 : Nat := 118140960795 + 4202495 * 2 ^ 59
def prefixEnd_4202495 : Nat := 4983230072969 + 3 ^ 40 * 4202495 * 2
def baseEnd_4202495 : Nat := 2157899883116640452685583

theorem tailTrace_4202495 : CollatzResearch.WordTrace tailWord_4202495 prefixEnd_4202495 2157899883116640452685583 := by
  unfold tailWord_4202495
  simp only [CollatzResearch.WordTrace]
  refine ⟨153277584910085818849784939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102185056606723879233189959 153277584910085818849784939)
  ·
    refine ⟨229916377365128728274677409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153277584910085818849784939 229916377365128728274677409)
    ·
      refine ⟨172437283023846546206008057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229916377365128728274677409 172437283023846546206008057)
      ·
        refine ⟨129327962267884909654506043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172437283023846546206008057 129327962267884909654506043)
        ·
          refine ⟨193991943401827364481759065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129327962267884909654506043 193991943401827364481759065)
          ·
            refine ⟨145493957551370523361319299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193991943401827364481759065 145493957551370523361319299)
            ·
              refine ⟨218240936327055785041978949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145493957551370523361319299 218240936327055785041978949)
              ·
                refine ⟨40920175561322959695371053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 218240936327055785041978949 40920175561322959695371053)
                ·
                  refine ⟨15345065835496109885764145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40920175561322959695371053 15345065835496109885764145)
                  ·
                    refine ⟨11508799376622082414323109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15345065835496109885764145 11508799376622082414323109)
                    ·
                      refine ⟨2157899883116640452685583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11508799376622082414323109 2157899883116640452685583)
                      ·
                        rfl

theorem cell23_4202495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_4202495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202495 prefixEnd_4202495 := by exact prefixLift 4202495
  have htrace : WordTrace (prefixWord ++ tailWord_4202495) baseStart_4202495 baseEnd_4202495 := by
    simpa [prefixWord, tailWord_4202495, baseEnd_4202495] using wordTrace_append hprefix tailTrace_4202495
  have hstable : (prefixWord ++ tailWord_4202495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202495).length < 2 ^ (prefixWord ++ tailWord_4202495).sum := by decide
  have hdescent : baseEnd_4202495 < baseStart_4202495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202522 : List Nat := [3, 1, 1, 3, 1, 3, 4, 7]
def baseStart_4202522 : Nat := 118140960795 + 4202522 * 2 ^ 59
def prefixEnd_4202522 : Nat := 4983230072969 + 3 ^ 40 * 4202522 * 2
def baseEnd_4202522 : Nat := 79922731373863401742517

theorem tailTrace_4202522 : CollatzResearch.WordTrace tailWord_4202522 prefixEnd_4202522 79922731373863401742517 := by
  unfold tailWord_4202522
  simp only [CollatzResearch.WordTrace]
  refine ⟨38319642420247000615254455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102185713120658668307345213 38319642420247000615254455)
  ·
    refine ⟨57479463630370500922881683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38319642420247000615254455 57479463630370500922881683)
    ·
      refine ⟨86219195445555751384322525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57479463630370500922881683 86219195445555751384322525)
      ·
        refine ⟨32332198292083406769120947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86219195445555751384322525 32332198292083406769120947)
        ·
          refine ⟨48498297438125110153681421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32332198292083406769120947 48498297438125110153681421)
          ·
            refine ⟨18186861539296916307630533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48498297438125110153681421 18186861539296916307630533)
            ·
              refine ⟨3410036538618171807680725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18186861539296916307630533 3410036538618171807680725)
              ·
                refine ⟨79922731373863401742517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3410036538618171807680725 79922731373863401742517)
                ·
                  rfl

theorem cell23_4202522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 7].length) (baseStart_4202522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202522 prefixEnd_4202522 := by exact prefixLift 4202522
  have htrace : WordTrace (prefixWord ++ tailWord_4202522) baseStart_4202522 baseEnd_4202522 := by
    simpa [prefixWord, tailWord_4202522, baseEnd_4202522] using wordTrace_append hprefix tailTrace_4202522
  have hstable : (prefixWord ++ tailWord_4202522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202522).length < 2 ^ (prefixWord ++ tailWord_4202522).sum := by decide
  have hdescent : baseEnd_4202522 < baseStart_4202522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202533 : List Nat := [1, 3, 1, 2, 2, 3, 3, 3, 1, 2, 2]
def baseStart_4202533 : Nat := 118140960795 + 4202533 * 2 ^ 59
def prefixEnd_4202533 : Nat := 4983230072969 + 3 ^ 40 * 4202533 * 2
def baseEnd_4202533 : Nat := 2157919395381511304010409

theorem tailTrace_4202533 : CollatzResearch.WordTrace tailWord_4202533 prefixEnd_4202533 2157919395381511304010409 := by
  unfold tailWord_4202533
  simp only [CollatzResearch.WordTrace]
  refine ⟨153278970883948151339668253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102185980589298767559778835 153278970883948151339668253)
  ·
    refine ⟨57479614081480556752375595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153278970883948151339668253 57479614081480556752375595)
    ·
      refine ⟨86219421122220835128563393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57479614081480556752375595 86219421122220835128563393)
      ·
        refine ⟨64664565841665626346422545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86219421122220835128563393 64664565841665626346422545)
        ·
          refine ⟨48498424381249219759816909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64664565841665626346422545 48498424381249219759816909)
          ·
            refine ⟨18186909142968457409931341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48498424381249219759816909 18186909142968457409931341)
            ·
              refine ⟨6820090928613171528724253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18186909142968457409931341 6820090928613171528724253)
              ·
                refine ⟨2557534098229939323271595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6820090928613171528724253 2557534098229939323271595)
                ·
                  refine ⟨3836301147344908984907393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2557534098229939323271595 3836301147344908984907393)
                  ·
                    refine ⟨2877225860508681738680545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3836301147344908984907393 2877225860508681738680545)
                    ·
                      refine ⟨2157919395381511304010409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2877225860508681738680545 2157919395381511304010409)
                      ·
                        rfl

theorem cell23_4202533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3, 1, 2, 2].length) (baseStart_4202533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202533 prefixEnd_4202533 := by exact prefixLift 4202533
  have htrace : WordTrace (prefixWord ++ tailWord_4202533) baseStart_4202533 baseEnd_4202533 := by
    simpa [prefixWord, tailWord_4202533, baseEnd_4202533] using wordTrace_append hprefix tailTrace_4202533
  have hstable : (prefixWord ++ tailWord_4202533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202533).length < 2 ^ (prefixWord ++ tailWord_4202533).sum := by decide
  have hdescent : baseEnd_4202533 < baseStart_4202533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202536 : List Nat := [2, 1, 5, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_4202536 : Nat := 118140960795 + 4202536 * 2 ^ 59
def prefixEnd_4202536 : Nat := 4983230072969 + 3 ^ 40 * 4202536 * 2
def baseEnd_4202536 : Nat := 2157920935823474792272895

theorem tailTrace_4202536 : CollatzResearch.WordTrace tailWord_4202536 prefixEnd_4202536 2157920935823474792272895 := by
  unfold tailWord_4202536
  simp only [CollatzResearch.WordTrace]
  refine ⟨76639540151468641426013731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102186053535291521901351641 76639540151468641426013731)
  ·
    refine ⟨114959310227202962139020597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76639540151468641426013731 114959310227202962139020597)
    ·
      refine ⟨10777435333800277700533181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114959310227202962139020597 10777435333800277700533181)
      ·
        refine ⟨4041538250175104137699943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10777435333800277700533181 4041538250175104137699943)
        ·
          refine ⟨6062307375262656206549915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4041538250175104137699943 6062307375262656206549915)
          ·
            refine ⟨9093461062893984309824873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6062307375262656206549915 9093461062893984309824873)
            ·
              refine ⟨6820095797170488232368655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9093461062893984309824873 6820095797170488232368655)
              ·
                refine ⟨10230143695755732348552983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6820095797170488232368655 10230143695755732348552983)
                ·
                  refine ⟨15345215543633598522829475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10230143695755732348552983 15345215543633598522829475)
                  ·
                    refine ⟨23017823315450397784244213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15345215543633598522829475 23017823315450397784244213)
                    ·
                      refine ⟨2157920935823474792272895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23017823315450397784244213 2157920935823474792272895)
                      ·
                        rfl

theorem cell23_4202536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_4202536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202536 prefixEnd_4202536 := by exact prefixLift 4202536
  have htrace : WordTrace (prefixWord ++ tailWord_4202536) baseStart_4202536 baseEnd_4202536 := by
    simpa [prefixWord, tailWord_4202536, baseEnd_4202536] using wordTrace_append hprefix tailTrace_4202536
  have hstable : (prefixWord ++ tailWord_4202536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202536).length < 2 ^ (prefixWord ++ tailWord_4202536).sum := by decide
  have hdescent : baseEnd_4202536 < baseStart_4202536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202549 : List Nat := [1, 3, 3, 1, 1, 1, 4, 1, 4, 1, 3]
def baseStart_4202549 : Nat := 118140960795 + 4202549 * 2 ^ 59
def prefixEnd_4202549 : Nat := 4983230072969 + 3 ^ 40 * 4202549 * 2
def baseEnd_4202549 : Nat := 2157927611071983241410335

theorem tailTrace_4202549 : CollatzResearch.WordTrace tailWord_4202549 prefixEnd_4202549 2157927611071983241410335 := by
  unfold tailWord_4202549
  simp only [CollatzResearch.WordTrace]
  refine ⟨153279554451890186072250701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102186369634593457381500467 153279554451890186072250701)
  ·
    refine ⟨57479832919458819777094013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153279554451890186072250701 57479832919458819777094013)
    ·
      refine ⟨21554937344797057416410255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57479832919458819777094013 21554937344797057416410255)
      ·
        refine ⟨32332406017195586124615383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21554937344797057416410255 32332406017195586124615383)
        ·
          refine ⟨48498609025793379186923075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32332406017195586124615383 48498609025793379186923075)
          ·
            refine ⟨72747913538690068780384613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48498609025793379186923075 72747913538690068780384613)
            ·
              refine ⟨13640233788504387896322115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72747913538690068780384613 13640233788504387896322115)
              ·
                refine ⟨20460350682756581844483173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13640233788504387896322115 20460350682756581844483173)
                ·
                  refine ⟨3836315753016859095840595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20460350682756581844483173 3836315753016859095840595)
                  ·
                    refine ⟨5754473629525288643760893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3836315753016859095840595 5754473629525288643760893)
                    ·
                      refine ⟨2157927611071983241410335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5754473629525288643760893 2157927611071983241410335)
                      ·
                        rfl

theorem cell23_4202549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_4202549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202549 prefixEnd_4202549 := by exact prefixLift 4202549
  have htrace : WordTrace (prefixWord ++ tailWord_4202549) baseStart_4202549 baseEnd_4202549 := by
    simpa [prefixWord, tailWord_4202549, baseEnd_4202549] using wordTrace_append hprefix tailTrace_4202549
  have hstable : (prefixWord ++ tailWord_4202549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202549).length < 2 ^ (prefixWord ++ tailWord_4202549).sum := by decide
  have hdescent : baseEnd_4202549 < baseStart_4202549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202555 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 4]
def baseStart_4202555 : Nat := 118140960795 + 4202555 * 2 ^ 59
def prefixEnd_4202555 : Nat := 4983230072969 + 3 ^ 40 * 4202555 * 2
def baseEnd_4202555 : Nat := 2157930691955910217935307

theorem tailTrace_4202555 : CollatzResearch.WordTrace tailWord_4202555 prefixEnd_4202555 2157930691955910217935307 := by
  unfold tailWord_4202555
  simp only [CollatzResearch.WordTrace]
  refine ⟨153279773289868449096969119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102186515526578966064646079 153279773289868449096969119)
  ·
    refine ⟨229919659934802673645453679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153279773289868449096969119 229919659934802673645453679)
    ·
      refine ⟨344879489902204010468180519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229919659934802673645453679 344879489902204010468180519)
      ·
        refine ⟨517319234853306015702270779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344879489902204010468180519 517319234853306015702270779)
        ·
          refine ⟨775978852279959023553406169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 517319234853306015702270779 775978852279959023553406169)
          ·
            refine ⟨581984139209969267665054627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 775978852279959023553406169 581984139209969267665054627)
            ·
              refine ⟨872976208814953901497581941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581984139209969267665054627 872976208814953901497581941)
              ·
                refine ⟨81841519576401928265398307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 872976208814953901497581941 81841519576401928265398307)
                ·
                  refine ⟨122762279364602892398097461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81841519576401928265398307 122762279364602892398097461)
                  ·
                    refine ⟨11508963690431521162321637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 122762279364602892398097461 11508963690431521162321637)
                    ·
                      refine ⟨2157930691955910217935307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11508963690431521162321637 2157930691955910217935307)
                      ·
                        rfl

theorem cell23_4202555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 4].length) (baseStart_4202555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202555 prefixEnd_4202555 := by exact prefixLift 4202555
  have htrace : WordTrace (prefixWord ++ tailWord_4202555) baseStart_4202555 baseEnd_4202555 := by
    simpa [prefixWord, tailWord_4202555, baseEnd_4202555] using wordTrace_append hprefix tailTrace_4202555
  have hstable : (prefixWord ++ tailWord_4202555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202555).length < 2 ^ (prefixWord ++ tailWord_4202555).sum := by decide
  have hdescent : baseEnd_4202555 < baseStart_4202555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202565 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 1, 8]
def baseStart_4202565 : Nat := 118140960795 + 4202565 * 2 ^ 59
def prefixEnd_4202565 : Nat := 4983230072969 + 3 ^ 40 * 4202565 * 2
def baseEnd_4202565 : Nat := 719311942254151726270087

theorem tailTrace_4202565 : CollatzResearch.WordTrace tailWord_4202565 prefixEnd_4202565 719311942254151726270087 := by
  unfold tailWord_4202565
  simp only [CollatzResearch.WordTrace]
  refine ⟨153280138019832220804833149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102186758679888147203222099 153280138019832220804833149)
  ·
    refine ⟨57480051757437082801812431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153280138019832220804833149 57480051757437082801812431)
    ·
      refine ⟨86220077636155624202718647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57480051757437082801812431 86220077636155624202718647)
      ·
        refine ⟨129330116454233436304077971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86220077636155624202718647 129330116454233436304077971)
        ·
          refine ⟨193995174681350154456116957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129330116454233436304077971 193995174681350154456116957)
          ·
            refine ⟨72748190505506307921043859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193995174681350154456116957 72748190505506307921043859)
            ·
              refine ⟨109122285758259461881565789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72748190505506307921043859 109122285758259461881565789)
              ·
                refine ⟨40920857159347298205587171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109122285758259461881565789 40920857159347298205587171)
                ·
                  refine ⟨61381285739020947308380757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40920857159347298205587171 61381285739020947308380757)
                  ·
                    refine ⟨719311942254151726270087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61381285739020947308380757 719311942254151726270087)
                    ·
                      rfl

theorem cell23_4202565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_4202565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202565 prefixEnd_4202565 := by exact prefixLift 4202565
  have htrace : WordTrace (prefixWord ++ tailWord_4202565) baseStart_4202565 baseEnd_4202565 := by
    simpa [prefixWord, tailWord_4202565, baseEnd_4202565] using wordTrace_append hprefix tailTrace_4202565
  have hstable : (prefixWord ++ tailWord_4202565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202565).length < 2 ^ (prefixWord ++ tailWord_4202565).sum := by decide
  have hdescent : baseEnd_4202565 < baseStart_4202565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202566 : List Nat := [6, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_4202566 : Nat := 118140960795 + 4202566 * 2 ^ 59
def prefixEnd_4202566 : Nat := 4983230072969 + 3 ^ 40 * 4202566 * 2
def baseEnd_4202566 : Nat := 2157936340243109674897757

theorem tailTrace_4202566 : CollatzResearch.WordTrace tailWord_4202566 prefixEnd_4202566 2157936340243109674897757 := by
  unfold tailWord_4202566
  simp only [CollatzResearch.WordTrace]
  refine ⟨4790005452900893686738111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 102186782995219065317079701 4790005452900893686738111)
  ·
    refine ⟨7185008179351340530107167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4790005452900893686738111 7185008179351340530107167)
    ·
      refine ⟨10777512269027010795160751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7185008179351340530107167 10777512269027010795160751)
      ·
        refine ⟨16166268403540516192741127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10777512269027010795160751 16166268403540516192741127)
        ·
          refine ⟨24249402605310774289111691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16166268403540516192741127 24249402605310774289111691)
          ·
            refine ⟨36374103907966161433667537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24249402605310774289111691 36374103907966161433667537)
            ·
              refine ⟨27280577930974621075250653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36374103907966161433667537 27280577930974621075250653)
              ·
                refine ⟨10230216724115482903218995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27280577930974621075250653 10230216724115482903218995)
                ·
                  refine ⟨15345325086173224354828493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10230216724115482903218995 15345325086173224354828493)
                  ·
                    refine ⟨5754496907314959133060685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15345325086173224354828493 5754496907314959133060685)
                    ·
                      refine ⟨2157936340243109674897757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5754496907314959133060685 2157936340243109674897757)
                      ·
                        rfl

theorem cell23_4202566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_4202566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202566 prefixEnd_4202566 := by exact prefixLift 4202566
  have htrace : WordTrace (prefixWord ++ tailWord_4202566) baseStart_4202566 baseEnd_4202566 := by
    simpa [prefixWord, tailWord_4202566, baseEnd_4202566] using wordTrace_append hprefix tailTrace_4202566
  have hstable : (prefixWord ++ tailWord_4202566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202566).length < 2 ^ (prefixWord ++ tailWord_4202566).sum := by decide
  have hdescent : baseEnd_4202566 < baseStart_4202566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202575 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 5]
def baseStart_4202575 : Nat := 118140960795 + 4202575 * 2 ^ 59
def prefixEnd_4202575 : Nat := 4983230072969 + 3 ^ 40 * 4202575 * 2
def baseEnd_4202575 : Nat := 2157940961569000139685215

theorem tailTrace_4202575 : CollatzResearch.WordTrace tailWord_4202575 prefixEnd_4202575 2157940961569000139685215 := by
  unfold tailWord_4202575
  simp only [CollatzResearch.WordTrace]
  refine ⟨153280502749795992512697179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102187001833197328341798119 153280502749795992512697179)
  ·
    refine ⟨229920754124693988769045769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153280502749795992512697179 229920754124693988769045769)
    ·
      refine ⟨172440565593520491576784327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229920754124693988769045769 172440565593520491576784327)
      ·
        refine ⟨258660848390280737365176491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172440565593520491576784327 258660848390280737365176491)
        ·
          refine ⟨387991272585421106047764737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258660848390280737365176491 387991272585421106047764737)
          ·
            refine ⟨290993454439065829535823553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387991272585421106047764737 290993454439065829535823553)
            ·
              refine ⟨218245090829299372151867665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290993454439065829535823553 218245090829299372151867665)
              ·
                refine ⟨163683818121974529113900749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218245090829299372151867665 163683818121974529113900749)
                ·
                  refine ⟨61381431795740448417712781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163683818121974529113900749 61381431795740448417712781)
                  ·
                    refine ⟨23018036923402668156642293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61381431795740448417712781 23018036923402668156642293)
                    ·
                      refine ⟨2157940961569000139685215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23018036923402668156642293 2157940961569000139685215)
                      ·
                        rfl

theorem cell23_4202575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 5].length) (baseStart_4202575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202575 prefixEnd_4202575 := by exact prefixLift 4202575
  have htrace : WordTrace (prefixWord ++ tailWord_4202575) baseStart_4202575 baseEnd_4202575 := by
    simpa [prefixWord, tailWord_4202575, baseEnd_4202575] using wordTrace_append hprefix tailTrace_4202575
  have hstable : (prefixWord ++ tailWord_4202575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202575).length < 2 ^ (prefixWord ++ tailWord_4202575).sum := by decide
  have hdescent : baseEnd_4202575 < baseStart_4202575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202592 : List Nat := [2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 5]
def baseStart_4202592 : Nat := 118140960795 + 4202592 * 2 ^ 59
def prefixEnd_4202592 : Nat := 4983230072969 + 3 ^ 40 * 4202592 * 2
def baseEnd_4202592 : Nat := 2157949690740126573172637

theorem tailTrace_4202592 : CollatzResearch.WordTrace tailWord_4202592 prefixEnd_4202592 2157949690740126573172637 := by
  unfold tailWord_4202592
  simp only [CollatzResearch.WordTrace]
  refine ⟨76640561395367202208033015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102187415193822936277377353 76640561395367202208033015)
  ·
    refine ⟨114960842093050803312049523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76640561395367202208033015 114960842093050803312049523)
    ·
      refine ⟨172441263139576204968074285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114960842093050803312049523 172441263139576204968074285)
      ·
        refine ⟨64665473677341076863027857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172441263139576204968074285 64665473677341076863027857)
        ·
          refine ⟨48499105258005807647270893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64665473677341076863027857 48499105258005807647270893)
          ·
            refine ⟨18187164471752177867726585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48499105258005807647270893 18187164471752177867726585)
            ·
              refine ⟨13640373353814133400794939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18187164471752177867726585 13640373353814133400794939)
              ·
                refine ⟨20460560030721200101192409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13640373353814133400794939 20460560030721200101192409)
                ·
                  refine ⟨15345420023040900075894307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20460560030721200101192409 15345420023040900075894307)
                  ·
                    refine ⟨23018130034561350113841461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15345420023040900075894307 23018130034561350113841461)
                    ·
                      refine ⟨2157949690740126573172637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23018130034561350113841461 2157949690740126573172637)
                      ·
                        rfl

theorem cell23_4202592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_4202592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202592 prefixEnd_4202592 := by exact prefixLift 4202592
  have htrace : WordTrace (prefixWord ++ tailWord_4202592) baseStart_4202592 baseEnd_4202592 := by
    simpa [prefixWord, tailWord_4202592, baseEnd_4202592] using wordTrace_append hprefix tailTrace_4202592
  have hstable : (prefixWord ++ tailWord_4202592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202592).length < 2 ^ (prefixWord ++ tailWord_4202592).sum := by decide
  have hdescent : baseEnd_4202592 < baseStart_4202592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202644 : List Nat := [2, 4, 2, 3, 2, 1, 2, 1, 1, 3, 2]
def baseStart_4202644 : Nat := 118140960795 + 4202644 * 2 ^ 59
def prefixEnd_4202644 : Nat := 4983230072969 + 3 ^ 40 * 4202644 * 2
def baseEnd_4202644 : Nat := 2157976391734160369722399

theorem tailTrace_4202644 : CollatzResearch.WordTrace tailWord_4202644 prefixEnd_4202644 2157976391734160369722399 := by
  unfold tailWord_4202644
  simp only [CollatzResearch.WordTrace]
  refine ⟨76641509693273008648479493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102188679591030678197972657 76641509693273008648479493)
  ·
    refine ⟨14370283067488689121589905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76641509693273008648479493 14370283067488689121589905)
    ·
      refine ⟨10777712300616516841192429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14370283067488689121589905 10777712300616516841192429)
      ·
        refine ⟨4041642112731193815447161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10777712300616516841192429 4041642112731193815447161)
        ·
          refine ⟨3031231584548395361585371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4041642112731193815447161 3031231584548395361585371)
          ·
            refine ⟨4546847376822593042378057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3031231584548395361585371 4546847376822593042378057)
            ·
              refine ⟨3410135532616944781783543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4546847376822593042378057 3410135532616944781783543)
              ·
                refine ⟨5115203298925417172675315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3410135532616944781783543 5115203298925417172675315)
                ·
                  refine ⟨7672804948388125759012973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5115203298925417172675315 7672804948388125759012973)
                  ·
                    refine ⟨2877301855645547159629865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7672804948388125759012973 2877301855645547159629865)
                    ·
                      refine ⟨2157976391734160369722399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2877301855645547159629865 2157976391734160369722399)
                      ·
                        rfl

theorem cell23_4202644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_4202644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202644 prefixEnd_4202644 := by exact prefixLift 4202644
  have htrace : WordTrace (prefixWord ++ tailWord_4202644) baseStart_4202644 baseEnd_4202644 := by
    simpa [prefixWord, tailWord_4202644, baseEnd_4202644] using wordTrace_append hprefix tailTrace_4202644
  have hstable : (prefixWord ++ tailWord_4202644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202644).length < 2 ^ (prefixWord ++ tailWord_4202644).sum := by decide
  have hdescent : baseEnd_4202644 < baseStart_4202644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202699 : List Nat := [1, 1, 1, 1, 3, 2, 4, 3, 2, 2, 3]
def baseStart_4202699 : Nat := 118140960795 + 4202699 * 2 ^ 59
def prefixEnd_4202699 : Nat := 4983230072969 + 3 ^ 40 * 4202699 * 2
def baseEnd_4202699 : Nat := 2158004633170157654534645

theorem tailTrace_4202699 : CollatzResearch.WordTrace tailWord_4202699 prefixEnd_4202699 2158004633170157654534645 := by
  unfold tailWord_4202699
  simp only [CollatzResearch.WordTrace]
  refine ⟨153285025401346761690211151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102190016934231174460140767 153285025401346761690211151)
  ·
    refine ⟨229927538102020142535316727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153285025401346761690211151 229927538102020142535316727)
    ·
      refine ⟨344891307153030213802975091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229927538102020142535316727 344891307153030213802975091)
      ·
        refine ⟨517336960729545320704462637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344891307153030213802975091 517336960729545320704462637)
        ·
          refine ⟨194001360273579495264173489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 517336960729545320704462637 194001360273579495264173489)
          ·
            refine ⟨145501020205184621448130117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194001360273579495264173489 145501020205184621448130117)
            ·
              refine ⟨27281441288472116521524397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145501020205184621448130117 27281441288472116521524397)
              ·
                refine ⟨10230540483177043695571649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27281441288472116521524397 10230540483177043695571649)
                ·
                  refine ⟨7672905362382782771678737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10230540483177043695571649 7672905362382782771678737)
                  ·
                    refine ⟨5754679021787087078759053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7672905362382782771678737 5754679021787087078759053)
                    ·
                      refine ⟨2158004633170157654534645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5754679021787087078759053 2158004633170157654534645)
                      ·
                        rfl

theorem cell23_4202699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2, 3].length) (baseStart_4202699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202699 prefixEnd_4202699 := by exact prefixLift 4202699
  have htrace : WordTrace (prefixWord ++ tailWord_4202699) baseStart_4202699 baseEnd_4202699 := by
    simpa [prefixWord, tailWord_4202699, baseEnd_4202699] using wordTrace_append hprefix tailTrace_4202699
  have hstable : (prefixWord ++ tailWord_4202699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202699).length < 2 ^ (prefixWord ++ tailWord_4202699).sum := by decide
  have hdescent : baseEnd_4202699 < baseStart_4202699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202763 : List Nat := [1, 1, 1, 1, 5, 2, 2, 5, 1, 1, 3]
def baseStart_4202763 : Nat := 118140960795 + 4202763 * 2 ^ 59
def prefixEnd_4202763 : Nat := 4983230072969 + 3 ^ 40 * 4202763 * 2
def baseEnd_4202763 : Nat := 2158037495932045404134351

theorem tailTrace_4202763 : CollatzResearch.WordTrace tailWord_4202763 prefixEnd_4202763 2158037495932045404134351 := by
  unfold tailWord_4202763
  simp only [CollatzResearch.WordTrace]
  refine ⟨153287359673114900620540943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102191573115409933747027295 153287359673114900620540943)
  ·
    refine ⟨229931039509672350930811415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153287359673114900620540943 229931039509672350930811415)
    ·
      refine ⟨344896559264508526396217123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229931039509672350930811415 344896559264508526396217123)
      ·
        refine ⟨517344838896762789594325685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344896559264508526396217123 517344838896762789594325685)
        ·
          refine ⟨48501078646571511524468033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 517344838896762789594325685 48501078646571511524468033)
          ·
            refine ⟨36375808984928633643351025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48501078646571511524468033 36375808984928633643351025)
            ·
              refine ⟨27281856738696475232513269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36375808984928633643351025 27281856738696475232513269)
              ·
                refine ⟨2557674069252794553048119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27281856738696475232513269 2557674069252794553048119)
                ·
                  refine ⟨3836511103879191829572179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2557674069252794553048119 3836511103879191829572179)
                  ·
                    refine ⟨5754766655818787744358269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3836511103879191829572179 5754766655818787744358269)
                    ·
                      refine ⟨2158037495932045404134351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5754766655818787744358269 2158037495932045404134351)
                      ·
                        rfl

theorem cell23_4202763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5, 1, 1, 3].length) (baseStart_4202763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202763 prefixEnd_4202763 := by exact prefixLift 4202763
  have htrace : WordTrace (prefixWord ++ tailWord_4202763) baseStart_4202763 baseEnd_4202763 := by
    simpa [prefixWord, tailWord_4202763, baseEnd_4202763] using wordTrace_append hprefix tailTrace_4202763
  have hstable : (prefixWord ++ tailWord_4202763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202763).length < 2 ^ (prefixWord ++ tailWord_4202763).sum := by decide
  have hdescent : baseEnd_4202763 < baseStart_4202763 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202779 : List Nat := [1, 1, 1, 1, 1, 1, 6, 3, 4, 4]
def baseStart_4202779 : Nat := 118140960795 + 4202779 * 2 ^ 59
def prefixEnd_4202779 : Nat := 4983230072969 + 3 ^ 40 * 4202779 * 2
def baseEnd_4202779 : Nat := 719348570540839113844759

theorem tailTrace_4202779 : CollatzResearch.WordTrace tailWord_4202779 prefixEnd_4202779 719348570540839113844759 := by
  unfold tailWord_4202779
  simp only [CollatzResearch.WordTrace]
  refine ⟨153287943241056935353123391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102191962160704623568748927 153287943241056935353123391)
  ·
    refine ⟨229931914861585403029685087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153287943241056935353123391 229931914861585403029685087)
    ·
      refine ⟨344897872292378104544527631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229931914861585403029685087 344897872292378104544527631)
      ·
        refine ⟨517346808438567156816791447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344897872292378104544527631 517346808438567156816791447)
        ·
          refine ⟨776020212657850735225187171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 517346808438567156816791447 776020212657850735225187171)
          ·
            refine ⟨1164030318986776102837780757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 776020212657850735225187171 1164030318986776102837780757)
            ·
              refine ⟨54563921202505129820520973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1164030318986776102837780757 54563921202505129820520973)
              ·
                refine ⟨20461470450939423682695365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54563921202505129820520973 20461470450939423682695365)
                ·
                  refine ⟨3836525709551141940505381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20461470450939423682695365 3836525709551141940505381)
                  ·
                    refine ⟨719348570540839113844759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3836525709551141940505381 719348570540839113844759)
                    ·
                      rfl

theorem cell23_4202779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4, 4].length) (baseStart_4202779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202779 prefixEnd_4202779 := by exact prefixLift 4202779
  have htrace : WordTrace (prefixWord ++ tailWord_4202779) baseStart_4202779 baseEnd_4202779 := by
    simpa [prefixWord, tailWord_4202779, baseEnd_4202779] using wordTrace_append hprefix tailTrace_4202779
  have hstable : (prefixWord ++ tailWord_4202779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202779).length < 2 ^ (prefixWord ++ tailWord_4202779).sum := by decide
  have hdescent : baseEnd_4202779 < baseStart_4202779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202786 : List Nat := [3, 3, 1, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_4202786 : Nat := 118140960795 + 4202786 * 2 ^ 59
def prefixEnd_4202786 : Nat := 4983230072969 + 3 ^ 40 * 4202786 * 2
def baseEnd_4202786 : Nat := 2158049305987098814146745

theorem tailTrace_4202786 : CollatzResearch.WordTrace tailWord_4202786 prefixEnd_4202786 2158049305987098814146745 := by
  unfold tailWord_4202786
  simp only [CollatzResearch.WordTrace]
  refine ⟨38322049638007893887157053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102192132368021050365752141 38322049638007893887157053)
  ·
    refine ⟨14370768614252960207683895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38322049638007893887157053 14370768614252960207683895)
    ·
      refine ⟨21556152921379440311525843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14370768614252960207683895 21556152921379440311525843)
      ·
        refine ⟨32334229382069160467288765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21556152921379440311525843 32334229382069160467288765)
        ·
          refine ⟨12125336018275935175233287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32334229382069160467288765 12125336018275935175233287)
          ·
            refine ⟨18188004027413902762849931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12125336018275935175233287 18188004027413902762849931)
            ·
              refine ⟨27282006041120854144274897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18188004027413902762849931 27282006041120854144274897)
              ·
                refine ⟨20461504530840640608206173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27282006041120854144274897 20461504530840640608206173)
                ·
                  refine ⟨7673064199065240228077315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20461504530840640608206173 7673064199065240228077315)
                  ·
                    refine ⟨11509596298597860342115973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7673064199065240228077315 11509596298597860342115973)
                    ·
                      refine ⟨2158049305987098814146745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11509596298597860342115973 2158049305987098814146745)
                      ·
                        rfl

theorem cell23_4202786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_4202786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202786 prefixEnd_4202786 := by exact prefixLift 4202786
  have htrace : WordTrace (prefixWord ++ tailWord_4202786) baseStart_4202786 baseEnd_4202786 := by
    simpa [prefixWord, tailWord_4202786, baseEnd_4202786] using wordTrace_append hprefix tailTrace_4202786
  have hstable : (prefixWord ++ tailWord_4202786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202786).length < 2 ^ (prefixWord ++ tailWord_4202786).sum := by decide
  have hdescent : baseEnd_4202786 < baseStart_4202786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202796 : List Nat := [2, 2, 1, 1, 1, 3, 4, 3, 2, 4]
def baseStart_4202796 : Nat := 118140960795 + 4202796 * 2 ^ 59
def prefixEnd_4202796 : Nat := 4983230072969 + 3 ^ 40 * 4202796 * 2
def baseEnd_4202796 : Nat := 719351480264547925007233

theorem tailTrace_4202796 : CollatzResearch.WordTrace tailWord_4202796 prefixEnd_4202796 719351480264547925007233 := by
  unfold tailWord_4202796
  simp only [CollatzResearch.WordTrace]
  refine ⟨76644281640997673628246121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102192375521330231504328161 76644281640997673628246121)
  ·
    refine ⟨57483211230748255221184591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76644281640997673628246121 57483211230748255221184591)
    ·
      refine ⟨86224816846122382831776887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57483211230748255221184591 86224816846122382831776887)
      ·
        refine ⟨129337225269183574247665331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86224816846122382831776887 129337225269183574247665331)
        ·
          refine ⟨194005837903775361371497997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129337225269183574247665331 194005837903775361371497997)
          ·
            refine ⟨72752189213915760514311749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 194005837903775361371497997 72752189213915760514311749)
            ·
              refine ⟨13641035477609205096433453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72752189213915760514311749 13641035477609205096433453)
              ·
                refine ⟨5115388304103451911162545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13641035477609205096433453 5115388304103451911162545)
                ·
                  refine ⟨3836541228077588933371909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5115388304103451911162545 3836541228077588933371909)
                  ·
                    refine ⟨719351480264547925007233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3836541228077588933371909 719351480264547925007233)
                    ·
                      rfl

theorem cell23_4202796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 4].length) (baseStart_4202796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202796 prefixEnd_4202796 := by exact prefixLift 4202796
  have htrace : WordTrace (prefixWord ++ tailWord_4202796) baseStart_4202796 baseEnd_4202796 := by
    simpa [prefixWord, tailWord_4202796, baseEnd_4202796] using wordTrace_append hprefix tailTrace_4202796
  have hstable : (prefixWord ++ tailWord_4202796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202796).length < 2 ^ (prefixWord ++ tailWord_4202796).sum := by decide
  have hdescent : baseEnd_4202796 < baseStart_4202796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202799 : List Nat := [1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 4]
def baseStart_4202799 : Nat := 118140960795 + 4202799 * 2 ^ 59
def prefixEnd_4202799 : Nat := 4983230072969 + 3 ^ 40 * 4202799 * 2
def baseEnd_4202799 : Nat := 2158055981235607263284185

theorem tailTrace_4202799 : CollatzResearch.WordTrace tailWord_4202799 prefixEnd_4202799 2158055981235607263284185 := by
  unfold tailWord_4202799
  simp only [CollatzResearch.WordTrace]
  refine ⟨153288672700984478768851451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102192448467322985845900967 153288672700984478768851451)
  ·
    refine ⟨229933009051476718153277177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153288672700984478768851451 229933009051476718153277177)
    ·
      refine ⟨172449756788607538614957883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229933009051476718153277177 172449756788607538614957883)
      ·
        refine ⟨258674635182911307922436825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172449756788607538614957883 258674635182911307922436825)
        ·
          refine ⟨194005976387183480941827619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258674635182911307922436825 194005976387183480941827619)
          ·
            refine ⟨291008964580775221412741429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194005976387183480941827619 291008964580775221412741429)
            ·
              refine ⟨27282090429447677007444509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 291008964580775221412741429 27282090429447677007444509)
              ·
                refine ⟨10230783911042878877791691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27282090429447677007444509 10230783911042878877791691)
                ·
                  refine ⟨15346175866564318316687537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10230783911042878877791691 15346175866564318316687537)
                  ·
                    refine ⟨11509631899923238737515653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15346175866564318316687537 11509631899923238737515653)
                    ·
                      refine ⟨2158055981235607263284185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11509631899923238737515653 2158055981235607263284185)
                      ·
                        rfl

theorem cell23_4202799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 4].length) (baseStart_4202799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202799 prefixEnd_4202799 := by exact prefixLift 4202799
  have htrace : WordTrace (prefixWord ++ tailWord_4202799) baseStart_4202799 baseEnd_4202799 := by
    simpa [prefixWord, tailWord_4202799, baseEnd_4202799] using wordTrace_append hprefix tailTrace_4202799
  have hstable : (prefixWord ++ tailWord_4202799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202799).length < 2 ^ (prefixWord ++ tailWord_4202799).sum := by decide
  have hdescent : baseEnd_4202799 < baseStart_4202799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202803 : List Nat := [1, 1, 1, 2, 5, 1, 3, 2, 3, 2, 2]
def baseStart_4202803 : Nat := 118140960795 + 4202803 * 2 ^ 59
def prefixEnd_4202803 : Nat := 4983230072969 + 3 ^ 40 * 4202803 * 2
def baseEnd_4202803 : Nat := 2158058035158225247634167

theorem tailTrace_4202803 : CollatzResearch.WordTrace tailWord_4202803 prefixEnd_4202803 2158058035158225247634167 := by
  unfold tailWord_4202803
  simp only [CollatzResearch.WordTrace]
  refine ⟨153288818592969987451997063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102192545728646658301331375 153288818592969987451997063)
  ·
    refine ⟨229933227889454981177995595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153288818592969987451997063 229933227889454981177995595)
    ·
      refine ⟨344899841834182471766993393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229933227889454981177995595 344899841834182471766993393)
      ·
        refine ⟨258674881375636853825245045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344899841834182471766993393 258674881375636853825245045)
        ·
          refine ⟨24250770128965955046116723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 258674881375636853825245045 24250770128965955046116723)
          ·
            refine ⟨36376155193448932569175085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24250770128965955046116723 36376155193448932569175085)
            ·
              refine ⟨13641058197543349713440657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36376155193448932569175085 13641058197543349713440657)
              ·
                refine ⟨10230793648157512285080493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13641058197543349713440657 10230793648157512285080493)
                ·
                  refine ⟨3836547618059067106905185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10230793648157512285080493 3836547618059067106905185)
                  ·
                    refine ⟨2877410713544300330178889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3836547618059067106905185 2877410713544300330178889)
                    ·
                      refine ⟨2158058035158225247634167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2877410713544300330178889 2158058035158225247634167)
                      ·
                        rfl

theorem cell23_4202803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3, 2, 2].length) (baseStart_4202803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202803 prefixEnd_4202803 := by exact prefixLift 4202803
  have htrace : WordTrace (prefixWord ++ tailWord_4202803) baseStart_4202803 baseEnd_4202803 := by
    simpa [prefixWord, tailWord_4202803, baseEnd_4202803] using wordTrace_append hprefix tailTrace_4202803
  have hstable : (prefixWord ++ tailWord_4202803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202803).length < 2 ^ (prefixWord ++ tailWord_4202803).sum := by decide
  have hdescent : baseEnd_4202803 < baseStart_4202803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202817 : List Nat := [1, 2, 5, 2, 3, 1, 2, 1, 1, 5]
def baseStart_4202817 : Nat := 118140960795 + 4202817 * 2 ^ 59
def prefixEnd_4202817 : Nat := 4983230072969 + 3 ^ 40 * 4202817 * 2
def baseEnd_4202817 : Nat := 719355074629129397619701

theorem tailTrace_4202817 : CollatzResearch.WordTrace tailWord_4202817 prefixEnd_4202817 719355074629129397619701 := by
  unfold tailWord_4202817
  simp only [CollatzResearch.WordTrace]
  refine ⟨153289329214919267843006705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102192886143279511895337803 153289329214919267843006705)
  ·
    refine ⟨114966996911189450882255029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153289329214919267843006705 114966996911189450882255029)
    ·
      refine ⟨10778155960424011020211409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114966996911189450882255029 10778155960424011020211409)
      ·
        refine ⟨8083616970318008265158557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10778155960424011020211409 8083616970318008265158557)
        ·
          refine ⟨3031356363869253099434459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8083616970318008265158557 3031356363869253099434459)
          ·
            refine ⟨4547034545803879649151689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3031356363869253099434459 4547034545803879649151689)
            ·
              refine ⟨3410275909352909736863767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4547034545803879649151689 3410275909352909736863767)
              ·
                refine ⟨5115413864029364605295651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3410275909352909736863767 5115413864029364605295651)
                ·
                  refine ⟨7673120796044046907943477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5115413864029364605295651 7673120796044046907943477)
                  ·
                    refine ⟨719355074629129397619701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7673120796044046907943477 719355074629129397619701)
                    ·
                      rfl

theorem cell23_4202817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_4202817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202817 prefixEnd_4202817 := by exact prefixLift 4202817
  have htrace : WordTrace (prefixWord ++ tailWord_4202817) baseStart_4202817 baseEnd_4202817 := by
    simpa [prefixWord, tailWord_4202817, baseEnd_4202817] using wordTrace_append hprefix tailTrace_4202817
  have hstable : (prefixWord ++ tailWord_4202817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202817).length < 2 ^ (prefixWord ++ tailWord_4202817).sum := by decide
  have hdescent : baseEnd_4202817 < baseStart_4202817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202820 : List Nat := [2, 3, 4, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_4202820 : Nat := 118140960795 + 4202820 * 2 ^ 59
def prefixEnd_4202820 : Nat := 4983230072969 + 3 ^ 40 * 4202820 * 2
def baseEnd_4202820 : Nat := 2158066764329351681121589

theorem tailTrace_4202820 : CollatzResearch.WordTrace tailWord_4202820 prefixEnd_4202820 2158066764329351681121589 := by
  unfold tailWord_4202820
  simp only [CollatzResearch.WordTrace]
  refine ⟨76644719316954199677682957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102192959089272266236910609 76644719316954199677682957)
  ·
    refine ⟨28741769743857824879131109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76644719316954199677682957 28741769743857824879131109)
    ·
      refine ⟨5389081826973342164837083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28741769743857824879131109 5389081826973342164837083)
      ·
        refine ⟨8083622740460013247255625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5389081826973342164837083 8083622740460013247255625)
        ·
          refine ⟨6062717055345009935441719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8083622740460013247255625 6062717055345009935441719)
          ·
            refine ⟨9094075583017514903162579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6062717055345009935441719 9094075583017514903162579)
            ·
              refine ⟨13641113374526272354743869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9094075583017514903162579 13641113374526272354743869)
              ·
                refine ⟨5115417515447352133028951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13641113374526272354743869 5115417515447352133028951)
                ·
                  refine ⟨7673126273171028199543427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5115417515447352133028951 7673126273171028199543427)
                  ·
                    refine ⟨11509689409756542299315141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7673126273171028199543427 11509689409756542299315141)
                    ·
                      refine ⟨2158066764329351681121589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11509689409756542299315141 2158066764329351681121589)
                      ·
                        rfl

theorem cell23_4202820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_4202820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202820 prefixEnd_4202820 := by exact prefixLift 4202820
  have htrace : WordTrace (prefixWord ++ tailWord_4202820) baseStart_4202820 baseEnd_4202820 := by
    simpa [prefixWord, tailWord_4202820, baseEnd_4202820] using wordTrace_append hprefix tailTrace_4202820
  have hstable : (prefixWord ++ tailWord_4202820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202820).length < 2 ^ (prefixWord ++ tailWord_4202820).sum := by decide
  have hdescent : baseEnd_4202820 < baseStart_4202820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202853 : List Nat := [1, 3, 1, 3, 1, 5, 1, 1, 1, 3, 3]
def baseStart_4202853 : Nat := 118140960795 + 4202853 * 2 ^ 59
def prefixEnd_4202853 : Nat := 4983230072969 + 3 ^ 40 * 4202853 * 2
def baseEnd_4202853 : Nat := 2158083709190950052008937

theorem tailTrace_4202853 : CollatzResearch.WordTrace tailWord_4202853 prefixEnd_4202853 2158083709190950052008937 := by
  unfold tailWord_4202853
  simp only [CollatzResearch.WordTrace]
  refine ⟨153290642242788845991317213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102193761495192563994211475 153290642242788845991317213)
  ·
    refine ⟨57483990841045817246743955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153290642242788845991317213 57483990841045817246743955)
    ·
      refine ⟨86225986261568725870115933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57483990841045817246743955 86225986261568725870115933)
      ·
        refine ⟨32334744848088272201293475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86225986261568725870115933 32334744848088272201293475)
        ·
          refine ⟨48502117272132408301940213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32334744848088272201293475 48502117272132408301940213)
          ·
            refine ⟨4547073494262413278306895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48502117272132408301940213 4547073494262413278306895)
            ·
              refine ⟨6820610241393619917460343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4547073494262413278306895 6820610241393619917460343)
              ·
                refine ⟨10230915362090429876190515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6820610241393619917460343 10230915362090429876190515)
                ·
                  refine ⟨15346373043135644814285773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10230915362090429876190515 15346373043135644814285773)
                  ·
                    refine ⟨5754889891175866805357165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15346373043135644814285773 5754889891175866805357165)
                    ·
                      refine ⟨2158083709190950052008937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5754889891175866805357165 2158083709190950052008937)
                      ·
                        rfl

theorem cell23_4202853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_4202853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202853 prefixEnd_4202853 := by exact prefixLift 4202853
  have htrace : WordTrace (prefixWord ++ tailWord_4202853) baseStart_4202853 baseEnd_4202853 := by
    simpa [prefixWord, tailWord_4202853, baseEnd_4202853] using wordTrace_append hprefix tailTrace_4202853
  have hstable : (prefixWord ++ tailWord_4202853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202853).length < 2 ^ (prefixWord ++ tailWord_4202853).sum := by decide
  have hdescent : baseEnd_4202853 < baseStart_4202853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202879 : List Nat := [1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 5]
def baseStart_4202879 : Nat := 118140960795 + 4202879 * 2 ^ 59
def prefixEnd_4202879 : Nat := 4983230072969 + 3 ^ 40 * 4202879 * 2
def baseEnd_4202879 : Nat := 2158097059687966950283817

theorem tailTrace_4202879 : CollatzResearch.WordTrace tailWord_4202879 prefixEnd_4202879 2158097059687966950283817 := by
  unfold tailWord_4202879
  simp only [CollatzResearch.WordTrace]
  refine ⟨153291590540694652431763691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102194393693796434954509127 153291590540694652431763691)
  ·
    refine ⟨229937385811041978647645537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153291590540694652431763691 229937385811041978647645537)
    ·
      refine ⟨172453039358281483985734153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229937385811041978647645537 172453039358281483985734153)
      ·
        refine ⟨129339779518711112989300615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172453039358281483985734153 129339779518711112989300615)
        ·
          refine ⟨194009669278066669483950923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129339779518711112989300615 194009669278066669483950923)
          ·
            refine ⟨291014503917100004225926385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194009669278066669483950923 291014503917100004225926385)
            ·
              refine ⟨218260877937825003169444789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 291014503917100004225926385 218260877937825003169444789)
              ·
                refine ⟨20461957306671094047135449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 218260877937825003169444789 20461957306671094047135449)
                ·
                  refine ⟨15346467980003320535351587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20461957306671094047135449 15346467980003320535351587)
                  ·
                    refine ⟨23019701970004980803027381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15346467980003320535351587 23019701970004980803027381)
                    ·
                      refine ⟨2158097059687966950283817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23019701970004980803027381 2158097059687966950283817)
                      ·
                        rfl

theorem cell23_4202879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_4202879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202879 prefixEnd_4202879 := by exact prefixLift 4202879
  have htrace : WordTrace (prefixWord ++ tailWord_4202879) baseStart_4202879 baseEnd_4202879 := by
    simpa [prefixWord, tailWord_4202879, baseEnd_4202879] using wordTrace_append hprefix tailTrace_4202879
  have hstable : (prefixWord ++ tailWord_4202879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202879).length < 2 ^ (prefixWord ++ tailWord_4202879).sum := by decide
  have hdescent : baseEnd_4202879 < baseStart_4202879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202959 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 2, 8]
def baseStart_4202959 : Nat := 118140960795 + 4202959 * 2 ^ 59
def prefixEnd_4202959 : Nat := 4983230072969 + 3 ^ 40 * 4202959 * 2
def baseEnd_4202959 : Nat := 719379379380108879094483

theorem tailTrace_4202959 : CollatzResearch.WordTrace tailWord_4202959 prefixEnd_4202959 719379379380108879094483 := by
  unfold tailWord_4202959
  simp only [CollatzResearch.WordTrace]
  refine ⟨153294508380404826094675931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102196338920269884063117287 153294508380404826094675931)
  ·
    refine ⟨229941762570607239142013897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153294508380404826094675931 229941762570607239142013897)
    ·
      refine ⟨172456321927955429356510423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229941762570607239142013897 172456321927955429356510423)
      ·
        refine ⟨258684482891933144034765635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172456321927955429356510423 258684482891933144034765635)
        ·
          refine ⟨388026724337899716052148453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258684482891933144034765635 388026724337899716052148453)
          ·
            refine ⟨72755010813356196759777835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 388026724337899716052148453 72755010813356196759777835)
            ·
              refine ⟨109132516220034295139666753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72755010813356196759777835 109132516220034295139666753)
              ·
                refine ⟨81849387165025721354750065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109132516220034295139666753 81849387165025721354750065)
                ·
                  refine ⟨61387040373769291016062549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81849387165025721354750065 61387040373769291016062549)
                  ·
                    refine ⟨719379379380108879094483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61387040373769291016062549 719379379380108879094483)
                    ·
                      rfl

theorem cell23_4202959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 8].length) (baseStart_4202959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202959 prefixEnd_4202959 := by exact prefixLift 4202959
  have htrace : WordTrace (prefixWord ++ tailWord_4202959) baseStart_4202959 baseEnd_4202959 := by
    simpa [prefixWord, tailWord_4202959, baseEnd_4202959] using wordTrace_append hprefix tailTrace_4202959
  have hstable : (prefixWord ++ tailWord_4202959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202959).length < 2 ^ (prefixWord ++ tailWord_4202959).sum := by decide
  have hdescent : baseEnd_4202959 < baseStart_4202959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4202983 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 1, 6, 2]
def baseStart_4202983 : Nat := 118140960795 + 4202983 * 2 ^ 59
def prefixEnd_4202983 : Nat := 4983230072969 + 3 ^ 40 * 4202983 * 2
def baseEnd_4202983 : Nat := 2158150461676034543383339

theorem tailTrace_4202983 : CollatzResearch.WordTrace tailWord_4202983 prefixEnd_4202983 2158150461676034543383339 := by
  unfold tailWord_4202983
  simp only [CollatzResearch.WordTrace]
  refine ⟨153295383732317878193549603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102196922488211918795699735 153295383732317878193549603)
  ·
    refine ⟨229943075598476817290324405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153295383732317878193549603 229943075598476817290324405)
    ·
      refine ⟨21557163337357201620967913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 229943075598476817290324405 21557163337357201620967913)
      ·
        refine ⟨16167872503017901215725935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21557163337357201620967913 16167872503017901215725935)
        ·
          refine ⟨24251808754526851823588903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16167872503017901215725935 24251808754526851823588903)
          ·
            refine ⟨36377713131790277735383355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24251808754526851823588903 36377713131790277735383355)
            ·
              refine ⟨54566569697685416603075033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36377713131790277735383355 54566569697685416603075033)
              ·
                refine ⟨40924927273264062452306275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54566569697685416603075033 40924927273264062452306275)
                ·
                  refine ⟨61387390909896093678459413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40924927273264062452306275 61387390909896093678459413)
                  ·
                    refine ⟨2877533948901379391177785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61387390909896093678459413 2877533948901379391177785)
                    ·
                      refine ⟨2158150461676034543383339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2877533948901379391177785 2158150461676034543383339)
                      ·
                        rfl

theorem cell23_4202983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_4202983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4202983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4202983 prefixEnd_4202983 := by exact prefixLift 4202983
  have htrace : WordTrace (prefixWord ++ tailWord_4202983) baseStart_4202983 baseEnd_4202983 := by
    simpa [prefixWord, tailWord_4202983, baseEnd_4202983] using wordTrace_append hprefix tailTrace_4202983
  have hstable : (prefixWord ++ tailWord_4202983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4202983).length < 2 ^ (prefixWord ++ tailWord_4202983).sum := by decide
  have hdescent : baseEnd_4202983 < baseStart_4202983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4202983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203096 : List Nat := [2, 1, 2, 2, 1, 2, 4, 9]
def baseStart_4203096 : Nat := 118140960795 + 4203096 * 2 ^ 59
def prefixEnd_4203096 : Nat := 4983230072969 + 3 ^ 40 * 4203096 * 2
def baseEnd_4203096 : Nat := 79933647592221948195197

theorem tailTrace_4203096 : CollatzResearch.WordTrace tailWord_4203096 prefixEnd_4203096 79933647592221948195197 := by
  unfold tailWord_4203096
  simp only [CollatzResearch.WordTrace]
  refine ⟨76649752590454249246206571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102199670120605665661608761 76649752590454249246206571)
  ·
    refine ⟨114974628885681373869309857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76649752590454249246206571 114974628885681373869309857)
    ·
      refine ⟨86230971664261030401982393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114974628885681373869309857 86230971664261030401982393)
      ·
        refine ⟨64673228748195772801486795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86230971664261030401982393 64673228748195772801486795)
        ·
          refine ⟨97009843122293659202230193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64673228748195772801486795 97009843122293659202230193)
          ·
            refine ⟨72757382341720244401672645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97009843122293659202230193 72757382341720244401672645)
            ·
              refine ⟨13642009189072545825313621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72757382341720244401672645 13642009189072545825313621)
              ·
                refine ⟨79933647592221948195197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13642009189072545825313621 79933647592221948195197)
                ·
                  rfl

theorem cell23_4203096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 9].length) (baseStart_4203096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203096 prefixEnd_4203096 := by exact prefixLift 4203096
  have htrace : WordTrace (prefixWord ++ tailWord_4203096) baseStart_4203096 baseEnd_4203096 := by
    simpa [prefixWord, tailWord_4203096, baseEnd_4203096] using wordTrace_append hprefix tailTrace_4203096
  have hstable : (prefixWord ++ tailWord_4203096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203096).length < 2 ^ (prefixWord ++ tailWord_4203096).sum := by decide
  have hdescent : baseEnd_4203096 < baseStart_4203096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203100 : List Nat := [2, 2, 4, 1, 3, 1, 1, 2, 1, 6]
def baseStart_4203100 : Nat := 118140960795 + 4203100 * 2 ^ 59
def prefixEnd_4203100 : Nat := 4983230072969 + 3 ^ 40 * 4203100 * 2
def baseEnd_4203100 : Nat := 719403512970870195206767

theorem tailTrace_4203100 : CollatzResearch.WordTrace tailWord_4203100 prefixEnd_4203100 719403512970870195206767 := by
  unfold tailWord_4203100
  simp only [CollatzResearch.WordTrace]
  refine ⟨76649825536447003587779377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102199767381929338117039169 76649825536447003587779377)
  ·
    refine ⟨57487369152335252690834533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76649825536447003587779377 57487369152335252690834533)
    ·
      refine ⟨10778881716062859879531475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57487369152335252690834533 10778881716062859879531475)
      ·
        refine ⟨16168322574094289819297213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10778881716062859879531475 16168322574094289819297213)
        ·
          refine ⟨6063120965285358682236455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16168322574094289819297213 6063120965285358682236455)
          ·
            refine ⟨9094681447928038023354683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6063120965285358682236455 9094681447928038023354683)
            ·
              refine ⟨13642022171892057035032025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9094681447928038023354683 13642022171892057035032025)
              ·
                refine ⟨10231516628919042776274019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13642022171892057035032025 10231516628919042776274019)
                ·
                  refine ⟨15347274943378564164411029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10231516628919042776274019 15347274943378564164411029)
                  ·
                    refine ⟨719403512970870195206767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15347274943378564164411029 719403512970870195206767)
                    ·
                      rfl

theorem cell23_4203100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_4203100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203100 prefixEnd_4203100 := by exact prefixLift 4203100
  have htrace : WordTrace (prefixWord ++ tailWord_4203100) baseStart_4203100 baseEnd_4203100 := by
    simpa [prefixWord, tailWord_4203100, baseEnd_4203100] using wordTrace_append hprefix tailTrace_4203100
  have hstable : (prefixWord ++ tailWord_4203100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203100).length < 2 ^ (prefixWord ++ tailWord_4203100).sum := by decide
  have hdescent : baseEnd_4203100 < baseStart_4203100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203117 : List Nat := [1, 5, 1, 1, 3, 2, 2, 2, 2, 4]
def baseStart_4203117 : Nat := 118140960795 + 4203117 * 2 ^ 59
def prefixEnd_4203117 : Nat := 4983230072969 + 3 ^ 40 * 4203117 * 2
def baseEnd_4203117 : Nat := 719406422694579006369241

theorem tailTrace_4203117 : CollatzResearch.WordTrace tailWord_4203117 prefixEnd_4203117 719406422694579006369241 := by
  unfold tailWord_4203117
  simp only [CollatzResearch.WordTrace]
  refine ⟨153300271113832419078927605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102200180742554946052618403 153300271113832419078927605)
  ·
    refine ⟨14371900416921789288649463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 153300271113832419078927605 14371900416921789288649463)
    ·
      refine ⟨21557850625382683932974195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14371900416921789288649463 21557850625382683932974195)
      ·
        refine ⟨32336775938074025899461293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21557850625382683932974195 32336775938074025899461293)
        ·
          refine ⟨12126290976777759712297985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32336775938074025899461293 12126290976777759712297985)
          ·
            refine ⟨9094718232583319784223489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12126290976777759712297985 9094718232583319784223489)
            ·
              refine ⟨6821038674437489838167617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9094718232583319784223489 6821038674437489838167617)
              ·
                refine ⟨5115779005828117378625713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6821038674437489838167617 5115779005828117378625713)
                ·
                  refine ⟨3836834254371088033969285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5115779005828117378625713 3836834254371088033969285)
                  ·
                    refine ⟨719406422694579006369241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3836834254371088033969285 719406422694579006369241)
                    ·
                      rfl

theorem cell23_4203117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_4203117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203117 prefixEnd_4203117 := by exact prefixLift 4203117
  have htrace : WordTrace (prefixWord ++ tailWord_4203117) baseStart_4203117 baseEnd_4203117 := by
    simpa [prefixWord, tailWord_4203117, baseEnd_4203117] using wordTrace_append hprefix tailTrace_4203117
  have hstable : (prefixWord ++ tailWord_4203117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203117).length < 2 ^ (prefixWord ++ tailWord_4203117).sum := by decide
  have hdescent : baseEnd_4203117 < baseStart_4203117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203140 : List Nat := [2, 3, 2, 1, 3, 1, 1, 3, 1, 3, 3]
def baseStart_4203140 : Nat := 118140960795 + 4203140 * 2 ^ 59
def prefixEnd_4203140 : Nat := 4983230072969 + 3 ^ 40 * 4203140 * 2
def baseEnd_4203140 : Nat := 2158231078138790429120117

theorem tailTrace_4203140 : CollatzResearch.WordTrace tailWord_4203140 prefixEnd_4203140 2158231078138790429120117 := by
  unfold tailWord_4203140
  simp only [CollatzResearch.WordTrace]
  refine ⟨76650554996374547003507437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102200739995166062671343249 76650554996374547003507437)
  ·
    refine ⟨28743958123640455126315289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76650554996374547003507437 28743958123640455126315289)
    ·
      refine ⟨21557968592730341344736467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28743958123640455126315289 21557968592730341344736467)
      ·
        refine ⟨32336952889095512017104701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21557968592730341344736467 32336952889095512017104701)
        ·
          refine ⟨12126357333410817006414263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32336952889095512017104701 12126357333410817006414263)
          ·
            refine ⟨18189536000116225509621395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12126357333410817006414263 18189536000116225509621395)
            ·
              refine ⟨27284304000174338264432093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18189536000116225509621395 27284304000174338264432093)
              ·
                refine ⟨10231614000065376849162035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27284304000174338264432093 10231614000065376849162035)
                ·
                  refine ⟨15347421000098065273743053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10231614000065376849162035 15347421000098065273743053)
                  ·
                    refine ⟨5755282875036774477653645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15347421000098065273743053 5755282875036774477653645)
                    ·
                      refine ⟨2158231078138790429120117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5755282875036774477653645 2158231078138790429120117)
                      ·
                        rfl

theorem cell23_4203140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_4203140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203140 prefixEnd_4203140 := by exact prefixLift 4203140
  have htrace : WordTrace (prefixWord ++ tailWord_4203140) baseStart_4203140 baseEnd_4203140 := by
    simpa [prefixWord, tailWord_4203140, baseEnd_4203140] using wordTrace_append hprefix tailTrace_4203140
  have hstable : (prefixWord ++ tailWord_4203140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203140).length < 2 ^ (prefixWord ++ tailWord_4203140).sum := by decide
  have hdescent : baseEnd_4203140 < baseStart_4203140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203197 : List Nat := [1, 4, 1, 2, 1, 3, 3, 1, 1, 4, 2]
def baseStart_4203197 : Nat := 118140960795 + 4203197 * 2 ^ 59
def prefixEnd_4203197 : Nat := 4983230072969 + 3 ^ 40 * 4203197 * 2
def baseEnd_4203197 : Nat := 2158260346536096706107355

theorem tailTrace_4203197 : CollatzResearch.WordTrace tailWord_4203197 prefixEnd_4203197 2158260346536096706107355 := by
  unfold tailWord_4203197
  simp only [CollatzResearch.WordTrace]
  refine ⟨153303188953542592741839845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102202125969028395161226563 153303188953542592741839845)
  ·
    refine ⟨28744347928789236139094971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153303188953542592741839845 28744347928789236139094971)
    ·
      refine ⟨43116521893183854208642457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28744347928789236139094971 43116521893183854208642457)
      ·
        refine ⟨32337391419887890656481843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43116521893183854208642457 32337391419887890656481843)
        ·
          refine ⟨48506087129831835984722765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32337391419887890656481843 48506087129831835984722765)
          ·
            refine ⟨18189782673686938494271037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48506087129831835984722765 18189782673686938494271037)
            ·
              refine ⟨6821168502632601935351639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18189782673686938494271037 6821168502632601935351639)
              ·
                refine ⟨10231752753948902903027459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6821168502632601935351639 10231752753948902903027459)
                ·
                  refine ⟨15347629130923354354541189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10231752753948902903027459 15347629130923354354541189)
                  ·
                    refine ⟨2877680462048128941476473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15347629130923354354541189 2877680462048128941476473)
                    ·
                      refine ⟨2158260346536096706107355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2877680462048128941476473 2158260346536096706107355)
                      ·
                        rfl

theorem cell23_4203197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_4203197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203197 prefixEnd_4203197 := by exact prefixLift 4203197
  have htrace : WordTrace (prefixWord ++ tailWord_4203197) baseStart_4203197 baseEnd_4203197 := by
    simpa [prefixWord, tailWord_4203197, baseEnd_4203197] using wordTrace_append hprefix tailTrace_4203197
  have hstable : (prefixWord ++ tailWord_4203197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203197).length < 2 ^ (prefixWord ++ tailWord_4203197).sum := by decide
  have hdescent : baseEnd_4203197 < baseStart_4203197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203283 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 6]
def baseStart_4203283 : Nat := 118140960795 + 4203283 * 2 ^ 59
def prefixEnd_4203283 : Nat := 4983230072969 + 3 ^ 40 * 4203283 * 2
def baseEnd_4203283 : Nat := 2158304505872383369631959

theorem tailTrace_4203283 : CollatzResearch.WordTrace tailWord_4203283 prefixEnd_4203283 2158304505872383369631959 := by
  unfold tailWord_4203283
  simp only [CollatzResearch.WordTrace]
  refine ⟨153306325631231029429470503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102204217087487352952980335 153306325631231029429470503)
  ·
    refine ⟨229959488446846544144205755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153306325631231029429470503 229959488446846544144205755)
    ·
      refine ⟨344939232670269816216308633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229959488446846544144205755 344939232670269816216308633)
      ·
        refine ⟨258704424502702362162231475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344939232670269816216308633 258704424502702362162231475)
        ·
          refine ⟨388056636754053543243347213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258704424502702362162231475 388056636754053543243347213)
          ·
            refine ⟨145521238782770078716255205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 388056636754053543243347213 145521238782770078716255205)
            ·
              refine ⟨27285232271769389759297851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145521238782770078716255205 27285232271769389759297851)
              ·
                refine ⟨40927848407654084638946777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27285232271769389759297851 40927848407654084638946777)
                ·
                  refine ⟨30695886305740563479210083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40927848407654084638946777 30695886305740563479210083)
                  ·
                    refine ⟨46043829458610845218815125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30695886305740563479210083 46043829458610845218815125)
                    ·
                      refine ⟨2158304505872383369631959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46043829458610845218815125 2158304505872383369631959)
                      ·
                        rfl

theorem cell23_4203283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 6].length) (baseStart_4203283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203283 prefixEnd_4203283 := by exact prefixLift 4203283
  have htrace : WordTrace (prefixWord ++ tailWord_4203283) baseStart_4203283 baseEnd_4203283 := by
    simpa [prefixWord, tailWord_4203283, baseEnd_4203283] using wordTrace_append hprefix tailTrace_4203283
  have hstable : (prefixWord ++ tailWord_4203283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203283).length < 2 ^ (prefixWord ++ tailWord_4203283).sum := by decide
  have hdescent : baseEnd_4203283 < baseStart_4203283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203347 : List Nat := [1, 1, 1, 2, 1, 1, 3, 6, 2, 3, 2]
def baseStart_4203347 : Nat := 118140960795 + 4203347 * 2 ^ 59
def prefixEnd_4203347 : Nat := 4983230072969 + 3 ^ 40 * 4203347 * 2
def baseEnd_4203347 : Nat := 2158337368634271119231665

theorem tailTrace_4203347 : CollatzResearch.WordTrace tailWord_4203347 prefixEnd_4203347 2158337368634271119231665 := by
  unfold tailWord_4203347
  simp only [CollatzResearch.WordTrace]
  refine ⟨153308659902999168359800295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102205773268666112239866863 153308659902999168359800295)
  ·
    refine ⟨229962989854498752539700443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153308659902999168359800295 229962989854498752539700443)
    ·
      refine ⟨344944484781748128809550665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229962989854498752539700443 344944484781748128809550665)
      ·
        refine ⟨258708363586311096607162999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344944484781748128809550665 258708363586311096607162999)
        ·
          refine ⟨388062545379466644910744499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258708363586311096607162999 388062545379466644910744499)
          ·
            refine ⟨582093818069199967366116749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 388062545379466644910744499 582093818069199967366116749)
            ·
              refine ⟨218285181775949987762293781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 582093818069199967366116749 218285181775949987762293781)
              ·
                refine ⟨10232117895747655676357521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 218285181775949987762293781 10232117895747655676357521)
                ·
                  refine ⟨7674088421810741757268141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10232117895747655676357521 7674088421810741757268141)
                  ·
                    refine ⟨2877783158179028158975553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7674088421810741757268141 2877783158179028158975553)
                    ·
                      refine ⟨2158337368634271119231665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2877783158179028158975553 2158337368634271119231665)
                      ·
                        rfl

theorem cell23_4203347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 3, 2].length) (baseStart_4203347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203347 prefixEnd_4203347 := by exact prefixLift 4203347
  have htrace : WordTrace (prefixWord ++ tailWord_4203347) baseStart_4203347 baseEnd_4203347 := by
    simpa [prefixWord, tailWord_4203347, baseEnd_4203347] using wordTrace_append hprefix tailTrace_4203347
  have hstable : (prefixWord ++ tailWord_4203347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203347).length < 2 ^ (prefixWord ++ tailWord_4203347).sum := by decide
  have hdescent : baseEnd_4203347 < baseStart_4203347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203354 : List Nat := [3, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3]
def baseStart_4203354 : Nat := 118140960795 + 4203354 * 2 ^ 59
def prefixEnd_4203354 : Nat := 4983230072969 + 3 ^ 40 * 4203354 * 2
def baseEnd_4203354 : Nat := 2158340962998852591844133

theorem tailTrace_4203354 : CollatzResearch.WordTrace tailWord_4203354 prefixEnd_4203354 2158340962998852591844133 := by
  unfold tailWord_4203354
  simp only [CollatzResearch.WordTrace]
  refine ⟨38327228803493452138826279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102205943475982539036870077 38327228803493452138826279)
  ·
    refine ⟨57490843205240178208239419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38327228803493452138826279 57490843205240178208239419)
    ·
      refine ⟨86236264807860267312359129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57490843205240178208239419 86236264807860267312359129)
      ·
        refine ⟨64677198605895200484269347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86236264807860267312359129 64677198605895200484269347)
        ·
          refine ⟨97015797908842800726404021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64677198605895200484269347 97015797908842800726404021)
          ·
            refine ⟨9095231053954012568100377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97015797908842800726404021 9095231053954012568100377)
            ·
              refine ⟨6821423290465509426075283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9095231053954012568100377 6821423290465509426075283)
              ·
                refine ⟨10232134935698264139112925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6821423290465509426075283 10232134935698264139112925)
                ·
                  refine ⟨3837050600886849052167347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10232134935698264139112925 3837050600886849052167347)
                  ·
                    refine ⟨5755575901330273578251021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3837050600886849052167347 5755575901330273578251021)
                    ·
                      refine ⟨2158340962998852591844133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5755575901330273578251021 2158340962998852591844133)
                      ·
                        rfl

theorem cell23_4203354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_4203354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203354 prefixEnd_4203354 := by exact prefixLift 4203354
  have htrace : WordTrace (prefixWord ++ tailWord_4203354) baseStart_4203354 baseEnd_4203354 := by
    simpa [prefixWord, tailWord_4203354, baseEnd_4203354] using wordTrace_append hprefix tailTrace_4203354
  have hstable : (prefixWord ++ tailWord_4203354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203354).length < 2 ^ (prefixWord ++ tailWord_4203354).sum := by decide
  have hdescent : baseEnd_4203354 < baseStart_4203354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203377 : List Nat := [1, 2, 2, 2, 1, 4, 1, 4, 1, 1, 4]
def baseStart_4203377 : Nat := 118140960795 + 4203377 * 2 ^ 59
def prefixEnd_4203377 : Nat := 4983230072969 + 3 ^ 40 * 4203377 * 2
def baseEnd_4203377 : Nat := 2158352773053906001856527

theorem tailTrace_4203377 : CollatzResearch.WordTrace tailWord_4203377 prefixEnd_4203377 2158352773053906001856527 := by
  unfold tailWord_4203377
  simp only [CollatzResearch.WordTrace]
  refine ⟨153309754092890483483392385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102206502728593655655594923 153309754092890483483392385)
  ·
    refine ⟨114982315569667862612544289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153309754092890483483392385 114982315569667862612544289)
    ·
      refine ⟨86236736677250896959408217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114982315569667862612544289 86236736677250896959408217)
      ·
        refine ⟨64677552507938172719556163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86236736677250896959408217 64677552507938172719556163)
        ·
          refine ⟨97016328761907259079334245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64677552507938172719556163 97016328761907259079334245)
          ·
            refine ⟨18190561642857611077375171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97016328761907259079334245 18190561642857611077375171)
            ·
              refine ⟨27285842464286416616062757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18190561642857611077375171 27285842464286416616062757)
              ·
                refine ⟨5116095462053703115511767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27285842464286416616062757 5116095462053703115511767)
                ·
                  refine ⟨7674143193080554673267651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5116095462053703115511767 7674143193080554673267651)
                  ·
                    refine ⟨11511214789620832009901477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7674143193080554673267651 11511214789620832009901477)
                    ·
                      refine ⟨2158352773053906001856527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11511214789620832009901477 2158352773053906001856527)
                      ·
                        rfl

theorem cell23_4203377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_4203377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203377 prefixEnd_4203377 := by exact prefixLift 4203377
  have htrace : WordTrace (prefixWord ++ tailWord_4203377) baseStart_4203377 baseEnd_4203377 := by
    simpa [prefixWord, tailWord_4203377, baseEnd_4203377] using wordTrace_append hprefix tailTrace_4203377
  have hstable : (prefixWord ++ tailWord_4203377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203377).length < 2 ^ (prefixWord ++ tailWord_4203377).sum := by decide
  have hdescent : baseEnd_4203377 < baseStart_4203377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
