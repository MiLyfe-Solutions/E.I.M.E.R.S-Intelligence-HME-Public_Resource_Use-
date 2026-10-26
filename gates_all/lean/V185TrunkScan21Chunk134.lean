import V185TrunkScan21Chunk133

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1633660 : List Nat := [2, 2, 2, 1, 1, 1, 7, 5]
def baseStart_1633660 : Nat := 118140960795 + 1633660 * 2 ^ 59
def prefixEnd_1633660 : Nat := 4983230072969 + 3 ^ 40 * 1633660 * 2
def baseEnd_1633660 : Nat := 124274489781360523175843

theorem tailTrace_1633660 : CollatzResearch.WordTrace tailWord_1633660 prefixEnd_1633660 124274489781360523175843 := by
  unfold tailWord_1633660
  simp only [CollatzResearch.WordTrace]
  refine ⟨29792237630768150880117217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39722983507690867840156289 29792237630768150880117217)
  ·
    refine ⟨22344178223076113160087913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29792237630768150880117217 22344178223076113160087913)
    ·
      refine ⟨16758133667307084870065935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22344178223076113160087913 16758133667307084870065935)
      ·
        refine ⟨25137200500960627305098903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16758133667307084870065935 25137200500960627305098903)
        ·
          refine ⟨37705800751440940957648355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25137200500960627305098903 37705800751440940957648355)
          ·
            refine ⟨56558701127161411436472533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37705800751440940957648355 56558701127161411436472533)
            ·
              refine ⟨1325594557667845580542325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 56558701127161411436472533 1325594557667845580542325)
              ·
                refine ⟨124274489781360523175843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1325594557667845580542325 124274489781360523175843)
                ·
                  rfl

theorem cell21_1633660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 5].length) (baseStart_1633660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1633660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1633660 prefixEnd_1633660 := by exact prefixLift 1633660
  have htrace : WordTrace (prefixWord ++ tailWord_1633660) baseStart_1633660 baseEnd_1633660 := by
    simpa [prefixWord, tailWord_1633660, baseEnd_1633660] using wordTrace_append hprefix tailTrace_1633660
  have hstable : (prefixWord ++ tailWord_1633660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633660).length < 2 ^ (prefixWord ++ tailWord_1633660).sum := by decide
  have hdescent : baseEnd_1633660 < baseStart_1633660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633666 : List Nat := [3, 4, 2, 1, 1, 2, 2, 3, 3]
def baseStart_1633666 : Nat := 118140960795 + 1633666 * 2 ^ 59
def prefixEnd_1633666 : Nat := 4983230072969 + 3 ^ 40 * 1633666 * 2
def baseEnd_1633666 : Nat := 372824838625826892427517

theorem tailTrace_1633666 : CollatzResearch.WordTrace tailWord_1633666 prefixEnd_1633666 372824838625826892427517 := by
  unfold tailWord_1633666
  simp only [CollatzResearch.WordTrace]
  refine ⟨14896173524878641196238213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39723129399676376523301901 14896173524878641196238213)
  ·
    refine ⟨2793032535914745224294665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14896173524878641196238213 2793032535914745224294665)
    ·
      refine ⟨2094774401936058918220999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2793032535914745224294665 2094774401936058918220999)
      ·
        refine ⟨3142161602904088377331499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2094774401936058918220999 3142161602904088377331499)
        ·
          refine ⟨4713242404356132565997249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3142161602904088377331499 4713242404356132565997249)
          ·
            refine ⟨3534931803267099424497937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4713242404356132565997249 3534931803267099424497937)
            ·
              refine ⟨2651198852450324568373453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3534931803267099424497937 2651198852450324568373453)
              ·
                refine ⟨994199569668871713140045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2651198852450324568373453 994199569668871713140045)
                ·
                  refine ⟨372824838625826892427517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 994199569668871713140045 372824838625826892427517)
                  ·
                    rfl

theorem cell21_1633666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_1633666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1633666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1633666 prefixEnd_1633666 := by exact prefixLift 1633666
  have htrace : WordTrace (prefixWord ++ tailWord_1633666) baseStart_1633666 baseEnd_1633666 := by
    simpa [prefixWord, tailWord_1633666, baseEnd_1633666] using wordTrace_append hprefix tailTrace_1633666
  have hstable : (prefixWord ++ tailWord_1633666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633666).length < 2 ^ (prefixWord ++ tailWord_1633666).sum := by decide
  have hdescent : baseEnd_1633666 < baseStart_1633666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633719 : List Nat := [1, 1, 3, 1, 3, 2, 3, 7]
def baseStart_1633719 : Nat := 118140960795 + 1633719 * 2 ^ 59
def prefixEnd_1633719 : Nat := 4983230072969 + 3 ^ 40 * 1633719 * 2
def baseEnd_1633719 : Nat := 124278977982636859348025

theorem tailTrace_1633719 : CollatzResearch.WordTrace tailWord_1633719 prefixEnd_1633719 124278977982636859348025 := by
  unfold tailWord_1633719
  simp only [CollatzResearch.WordTrace]
  refine ⟨59586627168322554836632211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39724418112215036557754807 59586627168322554836632211)
  ·
    refine ⟨89379940752483832254948317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59586627168322554836632211 89379940752483832254948317)
    ·
      refine ⟨33517477782181437095605619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89379940752483832254948317 33517477782181437095605619)
      ·
        refine ⟨50276216673272155643408429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33517477782181437095605619 50276216673272155643408429)
        ·
          refine ⟨18853581252477058366278161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50276216673272155643408429 18853581252477058366278161)
          ·
            refine ⟨14140185939357793774708621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18853581252477058366278161 14140185939357793774708621)
            ·
              refine ⟨5302569727259172665515733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14140185939357793774708621 5302569727259172665515733)
              ·
                refine ⟨124278977982636859348025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5302569727259172665515733 124278977982636859348025)
                ·
                  rfl

theorem cell21_1633719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 7].length) (baseStart_1633719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1633719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1633719 prefixEnd_1633719 := by exact prefixLift 1633719
  have htrace : WordTrace (prefixWord ++ tailWord_1633719) baseStart_1633719 baseEnd_1633719 := by
    simpa [prefixWord, tailWord_1633719, baseEnd_1633719] using wordTrace_append hprefix tailTrace_1633719
  have hstable : (prefixWord ++ tailWord_1633719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633719).length < 2 ^ (prefixWord ++ tailWord_1633719).sum := by decide
  have hdescent : baseEnd_1633719 < baseStart_1633719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633826 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 7]
def baseStart_1633826 : Nat := 118140960795 + 1633826 * 2 ^ 59
def prefixEnd_1633826 : Nat := 4983230072969 + 3 ^ 40 * 1633826 * 2
def baseEnd_1633826 : Nat := 372861352805702169760523

theorem tailTrace_1633826 : CollatzResearch.WordTrace tailWord_1633826 prefixEnd_1633826 372861352805702169760523 := by
  unfold tailWord_1633826
  simp only [CollatzResearch.WordTrace]
  refine ⟨14897632444733728027694333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39727019852623274740518221 14897632444733728027694333)
  ·
    refine ⟨5586612166775148010385375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14897632444733728027694333 5586612166775148010385375)
    ·
      refine ⟨8379918250162722015578063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5586612166775148010385375 8379918250162722015578063)
      ·
        refine ⟨12569877375244083023367095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8379918250162722015578063 12569877375244083023367095)
        ·
          refine ⟨18854816062866124535050643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12569877375244083023367095 18854816062866124535050643)
          ·
            refine ⟨28282224094299186802575965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18854816062866124535050643 28282224094299186802575965)
            ·
              refine ⟨10605834035362195050965987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28282224094299186802575965 10605834035362195050965987)
              ·
                refine ⟨15908751053043292576448981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10605834035362195050965987 15908751053043292576448981)
                ·
                  refine ⟨372861352805702169760523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15908751053043292576448981 372861352805702169760523)
                  ·
                    rfl

theorem cell21_1633826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_1633826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1633826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1633826 prefixEnd_1633826 := by exact prefixLift 1633826
  have htrace : WordTrace (prefixWord ++ tailWord_1633826) baseStart_1633826 baseEnd_1633826 := by
    simpa [prefixWord, tailWord_1633826, baseEnd_1633826] using wordTrace_append hprefix tailTrace_1633826
  have hstable : (prefixWord ++ tailWord_1633826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633826).length < 2 ^ (prefixWord ++ tailWord_1633826).sum := by decide
  have hdescent : baseEnd_1633826 < baseStart_1633826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633840 : List Nat := [2, 1, 1, 1, 2, 3, 1, 4, 6]
def baseStart_1633840 : Nat := 118140960795 + 1633840 * 2 ^ 59
def prefixEnd_1633840 : Nat := 4983230072969 + 3 ^ 40 * 1633840 * 2
def baseEnd_1633840 : Nat := 372864547796441256527161

theorem tailTrace_1633840 : CollatzResearch.WordTrace tailWord_1633840 prefixEnd_1633840 372864547796441256527161 := by
  unfold tailWord_1633840
  simp only [CollatzResearch.WordTrace]
  refine ⟨29795520200442096250893487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39727360267256128334524649 29795520200442096250893487)
  ·
    refine ⟨44693280300663144376340231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29795520200442096250893487 44693280300663144376340231)
    ·
      refine ⟨67039920450994716564510347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44693280300663144376340231 67039920450994716564510347)
      ·
        refine ⟨100559880676492074846765521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67039920450994716564510347 100559880676492074846765521)
        ·
          refine ⟨75419910507369056135074141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100559880676492074846765521 75419910507369056135074141)
          ·
            refine ⟨28282466440263396050652803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75419910507369056135074141 28282466440263396050652803)
            ·
              refine ⟨42423699660395094075979205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28282466440263396050652803 42423699660395094075979205)
              ·
                refine ⟨7954443686324080139246101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42423699660395094075979205 7954443686324080139246101)
                ·
                  refine ⟨372864547796441256527161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7954443686324080139246101 372864547796441256527161)
                  ·
                    rfl

theorem cell21_1633840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 6].length) (baseStart_1633840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1633840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1633840 prefixEnd_1633840 := by exact prefixLift 1633840
  have htrace : WordTrace (prefixWord ++ tailWord_1633840) baseStart_1633840 baseEnd_1633840 := by
    simpa [prefixWord, tailWord_1633840, baseEnd_1633840] using wordTrace_append hprefix tailTrace_1633840
  have hstable : (prefixWord ++ tailWord_1633840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633840).length < 2 ^ (prefixWord ++ tailWord_1633840).sum := by decide
  have hdescent : baseEnd_1633840 < baseStart_1633840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633843 : List Nat := [1, 1, 1, 2, 4, 3, 1, 5, 3]
def baseStart_1633843 : Nat := 118140960795 + 1633843 * 2 ^ 59
def prefixEnd_1633843 : Nat := 4983230072969 + 3 ^ 40 * 1633843 * 2
def baseEnd_1633843 : Nat := 372865232437313917977155

theorem tailTrace_1633843 : CollatzResearch.WordTrace tailWord_1633843 prefixEnd_1633843 372865232437313917977155 := by
  unfold tailWord_1633843
  simp only [CollatzResearch.WordTrace]
  refine ⟨59591149819873324014146183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39727433213248882676097455 59591149819873324014146183)
  ·
    refine ⟨89386724729809986021219275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59591149819873324014146183 89386724729809986021219275)
    ·
      refine ⟨134080087094714979031828913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89386724729809986021219275 134080087094714979031828913)
      ·
        refine ⟨100560065321036234273871685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134080087094714979031828913 100560065321036234273871685)
        ·
          refine ⟨18855012247694293926350941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100560065321036234273871685 18855012247694293926350941)
          ·
            refine ⟨7070629592885360222381603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18855012247694293926350941 7070629592885360222381603)
            ·
              refine ⟨10605944389328040333572405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7070629592885360222381603 10605944389328040333572405)
              ·
                refine ⟨994307286499503781272413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10605944389328040333572405 994307286499503781272413)
                ·
                  refine ⟨372865232437313917977155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 994307286499503781272413 372865232437313917977155)
                  ·
                    rfl

theorem cell21_1633843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5, 3].length) (baseStart_1633843 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1633843 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1633843 prefixEnd_1633843 := by exact prefixLift 1633843
  have htrace : WordTrace (prefixWord ++ tailWord_1633843) baseStart_1633843 baseEnd_1633843 := by
    simpa [prefixWord, tailWord_1633843, baseEnd_1633843] using wordTrace_append hprefix tailTrace_1633843
  have hstable : (prefixWord ++ tailWord_1633843).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633843).length < 2 ^ (prefixWord ++ tailWord_1633843).sum := by decide
  have hdescent : baseEnd_1633843 < baseStart_1633843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633857 : List Nat := [1, 2, 5, 1, 1, 1, 3, 1, 6]
def baseStart_1633857 : Nat := 118140960795 + 1633857 * 2 ^ 59
def prefixEnd_1633857 : Nat := 4983230072969 + 3 ^ 40 * 1633857 * 2
def baseEnd_1633857 : Nat := 372868427428053004743793

theorem tailTrace_1633857 : CollatzResearch.WordTrace tailWord_1633857 prefixEnd_1633857 372868427428053004743793 := by
  unfold tailWord_1633857
  simp only [CollatzResearch.WordTrace]
  refine ⟨59591660441822604405155825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39727773627881736270103883 59591660441822604405155825)
  ·
    refine ⟨44693745331366953303866869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59591660441822604405155825 44693745331366953303866869)
    ·
      refine ⟨4190038624815651872237519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44693745331366953303866869 4190038624815651872237519)
      ·
        refine ⟨6285057937223477808356279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4190038624815651872237519 6285057937223477808356279)
        ·
          refine ⟨9427586905835216712534419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6285057937223477808356279 9427586905835216712534419)
          ·
            refine ⟨14141380358752825068801629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9427586905835216712534419 14141380358752825068801629)
            ·
              refine ⟨5303017634532309400800611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14141380358752825068801629 5303017634532309400800611)
              ·
                refine ⟨7954526451798464101200917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5303017634532309400800611 7954526451798464101200917)
                ·
                  refine ⟨372868427428053004743793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7954526451798464101200917 372868427428053004743793)
                  ·
                    rfl

theorem cell21_1633857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 6].length) (baseStart_1633857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1633857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1633857 prefixEnd_1633857 := by exact prefixLift 1633857
  have htrace : WordTrace (prefixWord ++ tailWord_1633857) baseStart_1633857 baseEnd_1633857 := by
    simpa [prefixWord, tailWord_1633857, baseEnd_1633857] using wordTrace_append hprefix tailTrace_1633857
  have hstable : (prefixWord ++ tailWord_1633857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633857).length < 2 ^ (prefixWord ++ tailWord_1633857).sum := by decide
  have hdescent : baseEnd_1633857 < baseStart_1633857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634341 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 7]
def baseStart_1634341 : Nat := 118140960795 + 1634341 * 2 ^ 59
def prefixEnd_1634341 : Nat := 4983230072969 + 3 ^ 40 * 1634341 * 2
def baseEnd_1634341 : Nat := 372978882822175718676137

theorem tailTrace_1634341 : CollatzResearch.WordTrace tailWord_1634341 prefixEnd_1634341 372978882822175718676137 := by
  unfold tailWord_1634341
  simp only [CollatzResearch.WordTrace]
  refine ⟨59609313372069155065774877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39739542248046103377183251 59609313372069155065774877)
  ·
    refine ⟨22353492514525933149665579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59609313372069155065774877 22353492514525933149665579)
    ·
      refine ⟨33530238771788899724498369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22353492514525933149665579 33530238771788899724498369)
      ·
        refine ⟨25147679078841674793373777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33530238771788899724498369 25147679078841674793373777)
        ·
          refine ⟨18860759309131256095030333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25147679078841674793373777 18860759309131256095030333)
          ·
            refine ⟨7072784740924221035636375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18860759309131256095030333 7072784740924221035636375)
            ·
              refine ⟨10609177111386331553454563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7072784740924221035636375 10609177111386331553454563)
              ·
                refine ⟨15913765667079497330181845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10609177111386331553454563 15913765667079497330181845)
                ·
                  refine ⟨372978882822175718676137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15913765667079497330181845 372978882822175718676137)
                  ·
                    rfl

theorem cell21_1634341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_1634341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1634341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1634341 prefixEnd_1634341 := by exact prefixLift 1634341
  have htrace : WordTrace (prefixWord ++ tailWord_1634341) baseStart_1634341 baseEnd_1634341 := by
    simpa [prefixWord, tailWord_1634341, baseEnd_1634341] using wordTrace_append hprefix tailTrace_1634341
  have hstable : (prefixWord ++ tailWord_1634341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634341).length < 2 ^ (prefixWord ++ tailWord_1634341).sum := by decide
  have hdescent : baseEnd_1634341 < baseStart_1634341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634358 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_1634358 : Nat := 118140960795 + 1634358 * 2 ^ 59
def prefixEnd_1634358 : Nat := 4983230072969 + 3 ^ 40 * 1634358 * 2
def baseEnd_1634358 : Nat := 372982762453787466892769

theorem tailTrace_1634358 : CollatzResearch.WordTrace tailWord_1634358 prefixEnd_1634358 372982762453787466892769 := by
  unfold tailWord_1634358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3725620838312972935571483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39739955608671711312762485 3725620838312972935571483)
  ·
    refine ⟨5588431257469459403357225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3725620838312972935571483 5588431257469459403357225)
    ·
      refine ⟨4191323443102094552517919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5588431257469459403357225 4191323443102094552517919)
      ·
        refine ⟨6286985164653141828776879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4191323443102094552517919 6286985164653141828776879)
        ·
          refine ⟨9430477746979712743165319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6286985164653141828776879 9430477746979712743165319)
          ·
            refine ⟨14145716620469569114747979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9430477746979712743165319 14145716620469569114747979)
            ·
              refine ⟨21218574930704353672121969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14145716620469569114747979 21218574930704353672121969)
              ·
                refine ⟨15913931198028265254091477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21218574930704353672121969 15913931198028265254091477)
                ·
                  refine ⟨372982762453787466892769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15913931198028265254091477 372982762453787466892769)
                  ·
                    rfl

theorem cell21_1634358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_1634358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1634358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1634358 prefixEnd_1634358 := by exact prefixLift 1634358
  have htrace : WordTrace (prefixWord ++ tailWord_1634358) baseStart_1634358 baseEnd_1634358 := by
    simpa [prefixWord, tailWord_1634358, baseEnd_1634358] using wordTrace_append hprefix tailTrace_1634358
  have hstable : (prefixWord ++ tailWord_1634358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634358).length < 2 ^ (prefixWord ++ tailWord_1634358).sum := by decide
  have hdescent : baseEnd_1634358 < baseStart_1634358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634403 : List Nat := [1, 1, 1, 5, 1, 1, 6, 5]
def baseStart_1634403 : Nat := 118140960795 + 1634403 * 2 ^ 59
def prefixEnd_1634403 : Nat := 4983230072969 + 3 ^ 40 * 1634403 * 2
def baseEnd_1634403 : Nat := 124331010688959129547559

theorem tailTrace_1634403 : CollatzResearch.WordTrace tailWord_1634403 prefixEnd_1634403 124331010688959129547559 := by
  unfold tailWord_1634403
  simp only [CollatzResearch.WordTrace]
  refine ⟨59611574697844539654531863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39741049798563026436354575 59611574697844539654531863)
  ·
    refine ⟨89417362046766809481797795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59611574697844539654531863 89417362046766809481797795)
    ·
      refine ⟨134126043070150214222696693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89417362046766809481797795 134126043070150214222696693)
      ·
        refine ⟨12574316537826582583377815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134126043070150214222696693 12574316537826582583377815)
        ·
          refine ⟨18861474806739873875066723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12574316537826582583377815 18861474806739873875066723)
          ·
            refine ⟨28292212210109810812600085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18861474806739873875066723 28292212210109810812600085)
            ·
              refine ⟨1326197447348897381840629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28292212210109810812600085 1326197447348897381840629)
              ·
                refine ⟨124331010688959129547559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1326197447348897381840629 124331010688959129547559)
                ·
                  rfl

theorem cell21_1634403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 5].length) (baseStart_1634403 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1634403 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1634403 prefixEnd_1634403 := by exact prefixLift 1634403
  have htrace : WordTrace (prefixWord ++ tailWord_1634403) baseStart_1634403 baseEnd_1634403 := by
    simpa [prefixWord, tailWord_1634403, baseEnd_1634403] using wordTrace_append hprefix tailTrace_1634403
  have hstable : (prefixWord ++ tailWord_1634403).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634403).length < 2 ^ (prefixWord ++ tailWord_1634403).sum := by decide
  have hdescent : baseEnd_1634403 < baseStart_1634403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634448 : List Nat := [2, 1, 1, 1, 1, 1, 7, 3, 4]
def baseStart_1634448 : Nat := 118140960795 + 1634448 * 2 ^ 59
def prefixEnd_1634448 : Nat := 4983230072969 + 3 ^ 40 * 1634448 * 2
def baseEnd_1634448 : Nat := 373003301679967310392585

theorem tailTrace_1634448 : CollatzResearch.WordTrace tailWord_1634448 prefixEnd_1634448 373003301679967310392585 := by
  unfold tailWord_1634448
  simp only [CollatzResearch.WordTrace]
  refine ⟨29806607991340756169959999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39742143988454341559946665 29806607991340756169959999)
  ·
    refine ⟨44709911987011134254939999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29806607991340756169959999 44709911987011134254939999)
    ·
      refine ⟨67064867980516701382409999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44709911987011134254939999 67064867980516701382409999)
      ·
        refine ⟨100597301970775052073614999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67064867980516701382409999 100597301970775052073614999)
        ·
          refine ⟨150895952956162578110422499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100597301970775052073614999 150895952956162578110422499)
          ·
            refine ⟨226343929434243867165633749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150895952956162578110422499 226343929434243867165633749)
            ·
              refine ⟨5304935846115090636694541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 226343929434243867165633749 5304935846115090636694541)
              ·
                refine ⟨1989350942293158988760453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5304935846115090636694541 1989350942293158988760453)
                ·
                  refine ⟨373003301679967310392585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1989350942293158988760453 373003301679967310392585)
                  ·
                    rfl

theorem cell21_1634448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 4].length) (baseStart_1634448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1634448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1634448 prefixEnd_1634448 := by exact prefixLift 1634448
  have htrace : WordTrace (prefixWord ++ tailWord_1634448) baseStart_1634448 baseEnd_1634448 := by
    simpa [prefixWord, tailWord_1634448, baseEnd_1634448] using wordTrace_append hprefix tailTrace_1634448
  have hstable : (prefixWord ++ tailWord_1634448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634448).length < 2 ^ (prefixWord ++ tailWord_1634448).sum := by decide
  have hdescent : baseEnd_1634448 < baseStart_1634448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634493 : List Nat := [1, 4, 1, 2, 1, 1, 1, 5, 5]
def baseStart_1634493 : Nat := 118140960795 + 1634493 * 2 ^ 59
def prefixEnd_1634493 : Nat := 4983230072969 + 3 ^ 40 * 1634493 * 2
def baseEnd_1634493 : Nat := 373013571293057232142493

theorem tailTrace_1634493 : CollatzResearch.WordTrace tailWord_1634493 prefixEnd_1634493 373013571293057232142493 := by
  unfold tailWord_1634493
  simp only [CollatzResearch.WordTrace]
  refine ⟨59614857267518485025308133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39743238178345656683538755 59614857267518485025308133)
  ·
    refine ⟨11177785737659715942245275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59614857267518485025308133 11177785737659715942245275)
    ·
      refine ⟨16766678606489573913367913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11177785737659715942245275 16766678606489573913367913)
      ·
        refine ⟨12575008954867180435025935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16766678606489573913367913 12575008954867180435025935)
        ·
          refine ⟨18862513432300770652538903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12575008954867180435025935 18862513432300770652538903)
          ·
            refine ⟨28293770148451155978808355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18862513432300770652538903 28293770148451155978808355)
            ·
              refine ⟨42440655222676733968212533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28293770148451155978808355 42440655222676733968212533)
              ·
                refine ⟨3978811427125943809519925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42440655222676733968212533 3978811427125943809519925)
                ·
                  refine ⟨373013571293057232142493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3978811427125943809519925 373013571293057232142493)
                  ·
                    rfl

theorem cell21_1634493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_1634493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1634493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1634493 prefixEnd_1634493 := by exact prefixLift 1634493
  have htrace : WordTrace (prefixWord ++ tailWord_1634493) baseStart_1634493 baseEnd_1634493 := by
    simpa [prefixWord, tailWord_1634493, baseEnd_1634493] using wordTrace_append hprefix tailTrace_1634493
  have hstable : (prefixWord ++ tailWord_1634493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634493).length < 2 ^ (prefixWord ++ tailWord_1634493).sum := by decide
  have hdescent : baseEnd_1634493 < baseStart_1634493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634510 : List Nat := [4, 1, 1, 1, 4, 2, 1, 2, 5]
def baseStart_1634510 : Nat := 118140960795 + 1634510 * 2 ^ 59
def prefixEnd_1634510 : Nat := 4983230072969 + 3 ^ 40 * 1634510 * 2
def baseEnd_1634510 : Nat := 373017450924668980359125

theorem tailTrace_1634510 : CollatzResearch.WordTrace tailWord_1634510 prefixEnd_1634510 373017450924668980359125 := by
  unfold tailWord_1634510
  simp only [CollatzResearch.WordTrace]
  refine ⟨7451934663557112116084623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39743651538971264619117989 7451934663557112116084623)
  ·
    refine ⟨11177901995335668174126935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7451934663557112116084623 11177901995335668174126935)
    ·
      refine ⟨16766852993003502261190403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11177901995335668174126935 16766852993003502261190403)
      ·
        refine ⟨25150279489505253391785605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16766852993003502261190403 25150279489505253391785605)
        ·
          refine ⟨4715677404282235010959801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25150279489505253391785605 4715677404282235010959801)
          ·
            refine ⟨3536758053211676258219851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4715677404282235010959801 3536758053211676258219851)
            ·
              refine ⟨5305137079817514387329777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3536758053211676258219851 5305137079817514387329777)
              ·
                refine ⟨3978852809863135790497333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5305137079817514387329777 3978852809863135790497333)
                ·
                  refine ⟨373017450924668980359125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3978852809863135790497333 373017450924668980359125)
                  ·
                    rfl

theorem cell21_1634510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_1634510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1634510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1634510 prefixEnd_1634510 := by exact prefixLift 1634510
  have htrace : WordTrace (prefixWord ++ tailWord_1634510) baseStart_1634510 baseEnd_1634510 := by
    simpa [prefixWord, tailWord_1634510, baseEnd_1634510] using wordTrace_append hprefix tailTrace_1634510
  have hstable : (prefixWord ++ tailWord_1634510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634510).length < 2 ^ (prefixWord ++ tailWord_1634510).sum := by decide
  have hdescent : baseEnd_1634510 < baseStart_1634510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634538 : List Nat := [3, 1, 3, 1, 1, 2, 10]
def baseStart_1634538 : Nat := 118140960795 + 1634538 * 2 ^ 59
def prefixEnd_1634538 : Nat := 4983230072969 + 3 ^ 40 * 1634538 * 2
def baseEnd_1634538 : Nat := 41447093434016350432489

theorem tailTrace_1634538 : CollatzResearch.WordTrace tailWord_1634538 prefixEnd_1634538 41447093434016350432489 := by
  unfold tailWord_1634538
  simp only [CollatzResearch.WordTrace]
  refine ⟨14904124638088864427674067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39744332368236971807130845 14904124638088864427674067)
  ·
    refine ⟨22356186957133296641511101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14904124638088864427674067 22356186957133296641511101)
    ·
      refine ⟨8383570108924986240566663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22356186957133296641511101 8383570108924986240566663)
      ·
        refine ⟨12575355163387479360849995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8383570108924986240566663 12575355163387479360849995)
        ·
          refine ⟨18863032745081219041274993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12575355163387479360849995 18863032745081219041274993)
          ·
            refine ⟨14147274558810914280956245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18863032745081219041274993 14147274558810914280956245)
            ·
              refine ⟨41447093434016350432489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14147274558810914280956245 41447093434016350432489)
              ·
                rfl

theorem cell21_1634538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 10].length) (baseStart_1634538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1634538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1634538 prefixEnd_1634538 := by exact prefixLift 1634538
  have htrace : WordTrace (prefixWord ++ tailWord_1634538) baseStart_1634538 baseEnd_1634538 := by
    simpa [prefixWord, tailWord_1634538, baseEnd_1634538] using wordTrace_append hprefix tailTrace_1634538
  have hstable : (prefixWord ++ tailWord_1634538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634538).length < 2 ^ (prefixWord ++ tailWord_1634538).sum := by decide
  have hdescent : baseEnd_1634538 < baseStart_1634538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634541 : List Nat := [1, 5, 1, 2, 3, 1, 1, 1, 6]
def baseStart_1634541 : Nat := 118140960795 + 1634541 * 2 ^ 59
def prefixEnd_1634541 : Nat := 4983230072969 + 3 ^ 40 * 1634541 * 2
def baseEnd_1634541 : Nat := 373024525547019815342395

theorem tailTrace_1634541 : CollatzResearch.WordTrace tailWord_1634541 prefixEnd_1634541 373024525547019815342395 := by
  unfold tailWord_1634541
  simp only [CollatzResearch.WordTrace]
  refine ⟨59616607971344589223055477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39744405314229726148703651 59616607971344589223055477)
  ·
    refine ⟨5589056997313555239661451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59616607971344589223055477 5589056997313555239661451)
    ·
      refine ⟨8383585495970332859492177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5589056997313555239661451 8383585495970332859492177)
      ·
        refine ⟨6287689121977749644619133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8383585495970332859492177 6287689121977749644619133)
        ·
          refine ⟨2357883420741656116732175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6287689121977749644619133 2357883420741656116732175)
          ·
            refine ⟨3536825131112484175098263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2357883420741656116732175 3536825131112484175098263)
            ·
              refine ⟨5305237696668726262647395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3536825131112484175098263 5305237696668726262647395)
              ·
                refine ⟨7957856545003089393971093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5305237696668726262647395 7957856545003089393971093)
                ·
                  refine ⟨373024525547019815342395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7957856545003089393971093 373024525547019815342395)
                  ·
                    rfl

theorem cell21_1634541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_1634541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1634541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1634541 prefixEnd_1634541 := by exact prefixLift 1634541
  have htrace : WordTrace (prefixWord ++ tailWord_1634541) baseStart_1634541 baseEnd_1634541 := by
    simpa [prefixWord, tailWord_1634541, baseEnd_1634541] using wordTrace_append hprefix tailTrace_1634541
  have hstable : (prefixWord ++ tailWord_1634541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634541).length < 2 ^ (prefixWord ++ tailWord_1634541).sum := by decide
  have hdescent : baseEnd_1634541 < baseStart_1634541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634558 : List Nat := [4, 2, 2, 1, 1, 1, 5, 1, 4]
def baseStart_1634558 : Nat := 118140960795 + 1634558 * 2 ^ 59
def prefixEnd_1634558 : Nat := 4983230072969 + 3 ^ 40 * 1634558 * 2
def baseEnd_1634558 : Nat := 373028405178631563559027

theorem tailTrace_1634558 : CollatzResearch.WordTrace tailWord_1634558 prefixEnd_1634558 373028405178631563559027 := by
  unfold tailWord_1634558
  simp only [CollatzResearch.WordTrace]
  refine ⟨7452153501535375140803041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39744818674855334084282885 7452153501535375140803041)
  ·
    refine ⟨5589115126151531355602281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7452153501535375140803041 5589115126151531355602281)
    ·
      refine ⟨4191836344613648516701711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5589115126151531355602281 4191836344613648516701711)
      ·
        refine ⟨6287754516920472775052567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4191836344613648516701711 6287754516920472775052567)
        ·
          refine ⟨9431631775380709162578851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6287754516920472775052567 9431631775380709162578851)
          ·
            refine ⟨14147447663071063743868277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9431631775380709162578851 14147447663071063743868277)
            ·
              refine ⟨1326323218412912225987651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14147447663071063743868277 1326323218412912225987651)
              ·
                refine ⟨1989484827619368338981477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1326323218412912225987651 1989484827619368338981477)
                ·
                  refine ⟨373028405178631563559027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1989484827619368338981477 373028405178631563559027)
                  ·
                    rfl

theorem cell21_1634558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_1634558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1634558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1634558 prefixEnd_1634558 := by exact prefixLift 1634558
  have htrace : WordTrace (prefixWord ++ tailWord_1634558) baseStart_1634558 baseEnd_1634558 := by
    simpa [prefixWord, tailWord_1634558, baseEnd_1634558] using wordTrace_append hprefix tailTrace_1634558
  have hstable : (prefixWord ++ tailWord_1634558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634558).length < 2 ^ (prefixWord ++ tailWord_1634558).sum := by decide
  have hdescent : baseEnd_1634558 < baseStart_1634558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634569 : List Nat := [1, 2, 1, 1, 3, 4, 2, 2, 5]
def baseStart_1634569 : Nat := 118140960795 + 1634569 * 2 ^ 59
def prefixEnd_1634569 : Nat := 4983230072969 + 3 ^ 40 * 1634569 * 2
def baseEnd_1634569 : Nat := 373030915528497988875671

theorem tailTrace_1634569 : CollatzResearch.WordTrace tailWord_1634569 prefixEnd_1634569 373030915528497988875671 := by
  unfold tailWord_1634569
  simp only [CollatzResearch.WordTrace]
  refine ⟨59617629215243150005074761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39745086143495433336716507 59617629215243150005074761)
  ·
    refine ⟨44713221911432362503806071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59617629215243150005074761 44713221911432362503806071)
    ·
      refine ⟨67069832867148543755709107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44713221911432362503806071 67069832867148543755709107)
      ·
        refine ⟨100604749300722815633563661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67069832867148543755709107 100604749300722815633563661)
        ·
          refine ⟨37726780987771055862586373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100604749300722815633563661 37726780987771055862586373)
          ·
            refine ⟨7073771435207072974234945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37726780987771055862586373 7073771435207072974234945)
            ·
              refine ⟨5305328576405304730676209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7073771435207072974234945 5305328576405304730676209)
              ·
                refine ⟨3978996432303978548007157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5305328576405304730676209 3978996432303978548007157)
                ·
                  refine ⟨373030915528497988875671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3978996432303978548007157 373030915528497988875671)
                  ·
                    rfl

theorem cell21_1634569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 5].length) (baseStart_1634569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1634569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1634569 prefixEnd_1634569 := by exact prefixLift 1634569
  have htrace : WordTrace (prefixWord ++ tailWord_1634569) baseStart_1634569 baseEnd_1634569 := by
    simpa [prefixWord, tailWord_1634569, baseEnd_1634569] using wordTrace_append hprefix tailTrace_1634569
  have hstable : (prefixWord ++ tailWord_1634569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634569).length < 2 ^ (prefixWord ++ tailWord_1634569).sum := by decide
  have hdescent : baseEnd_1634569 < baseStart_1634569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634617 : List Nat := [1, 2, 1, 6, 1, 2, 1, 3, 4]
def baseStart_1634617 : Nat := 118140960795 + 1634617 * 2 ^ 59
def prefixEnd_1634617 : Nat := 4983230072969 + 3 ^ 40 * 1634617 * 2
def baseEnd_1634617 : Nat := 373041869782460572075573

theorem tailTrace_1634617 : CollatzResearch.WordTrace tailWord_1634617 prefixEnd_1634617 373041869782460572075573 := by
  unfold tailWord_1634617
  simp only [CollatzResearch.WordTrace]
  refine ⟨59619379919069254202822105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39746253279379502801881403 59619379919069254202822105)
  ·
    refine ⟨44714534939301940652116579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59619379919069254202822105 44714534939301940652116579)
    ·
      refine ⟨67071802408952910978174869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44714534939301940652116579 67071802408952910978174869)
      ·
        refine ⟨3143990737919667702101947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67071802408952910978174869 3143990737919667702101947)
        ·
          refine ⟨4715986106879501553152921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3143990737919667702101947 4715986106879501553152921)
          ·
            refine ⟨3536989580159626164864691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4715986106879501553152921 3536989580159626164864691)
            ·
              refine ⟨5305484370239439247297037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3536989580159626164864691 5305484370239439247297037)
              ·
                refine ⟨1989556638839789717736389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5305484370239439247297037 1989556638839789717736389)
                ·
                  refine ⟨373041869782460572075573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1989556638839789717736389 373041869782460572075573)
                  ·
                    rfl

theorem cell21_1634617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 4].length) (baseStart_1634617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1634617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1634617 prefixEnd_1634617 := by exact prefixLift 1634617
  have htrace : WordTrace (prefixWord ++ tailWord_1634617) baseStart_1634617 baseEnd_1634617 := by
    simpa [prefixWord, tailWord_1634617, baseEnd_1634617] using wordTrace_append hprefix tailTrace_1634617
  have hstable : (prefixWord ++ tailWord_1634617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634617).length < 2 ^ (prefixWord ++ tailWord_1634617).sum := by decide
  have hdescent : baseEnd_1634617 < baseStart_1634617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634741 : List Nat := [1, 3, 3, 2, 4, 1, 2, 5]
def baseStart_1634741 : Nat := 118140960795 + 1634741 * 2 ^ 59
def prefixEnd_1634741 : Nat := 4983230072969 + 3 ^ 40 * 1634741 * 2
def baseEnd_1634741 : Nat := 124356722757287970669551

theorem tailTrace_1634741 : CollatzResearch.WordTrace tailWord_1634741 prefixEnd_1634741 124356722757287970669551 := by
  unfold tailWord_1634741
  simp only [CollatzResearch.WordTrace]
  refine ⟨59623902570620023380336077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39749268380413348920224051 59623902570620023380336077)
  ·
    refine ⟨22358963463982508767626029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59623902570620023380336077 22358963463982508767626029)
    ·
      refine ⟨8384611298993440787859761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22358963463982508767626029 8384611298993440787859761)
      ·
        refine ⟨6288458474245080590894821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8384611298993440787859761 6288458474245080590894821)
        ·
          refine ⟨1179085963920952610792779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6288458474245080590894821 1179085963920952610792779)
          ·
            refine ⟨1768628945881428916189169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1179085963920952610792779 1768628945881428916189169)
            ·
              refine ⟨1326471709411071687141877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1768628945881428916189169 1326471709411071687141877)
              ·
                refine ⟨124356722757287970669551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1326471709411071687141877 124356722757287970669551)
                ·
                  rfl

theorem cell21_1634741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 5].length) (baseStart_1634741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1634741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1634741 prefixEnd_1634741 := by exact prefixLift 1634741
  have htrace : WordTrace (prefixWord ++ tailWord_1634741) baseStart_1634741 baseEnd_1634741 := by
    simpa [prefixWord, tailWord_1634741, baseEnd_1634741] using wordTrace_append hprefix tailTrace_1634741
  have hstable : (prefixWord ++ tailWord_1634741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634741).length < 2 ^ (prefixWord ++ tailWord_1634741).sum := by decide
  have hdescent : baseEnd_1634741 < baseStart_1634741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634772 : List Nat := [2, 4, 1, 2, 2, 2, 3, 2, 3]
def baseStart_1634772 : Nat := 118140960795 + 1634772 * 2 ^ 59
def prefixEnd_1634772 : Nat := 4983230072969 + 3 ^ 40 * 1634772 * 2
def baseEnd_1634772 : Nat := 373077242894214746991923

theorem tailTrace_1634772 : CollatzResearch.WordTrace tailWord_1634772 prefixEnd_1634772 373077242894214746991923 := by
  unfold tailWord_1634772
  simp only [CollatzResearch.WordTrace]
  refine ⟨29812516616753857837357285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39750022155671810449809713 29812516616753857837357285)
  ·
    refine ⟨5589846865641348344504491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29812516616753857837357285 5589846865641348344504491)
    ·
      refine ⟨8384770298462022516756737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5589846865641348344504491 8384770298462022516756737)
      ·
        refine ⟨6288577723846516887567553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8384770298462022516756737 6288577723846516887567553)
        ·
          refine ⟨4716433292884887665675665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6288577723846516887567553 4716433292884887665675665)
          ·
            refine ⟨3537324969663665749256749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4716433292884887665675665 3537324969663665749256749)
            ·
              refine ⟨1326496863623874655971281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3537324969663665749256749 1326496863623874655971281)
              ·
                refine ⟨994872647717905991978461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1326496863623874655971281 994872647717905991978461)
                ·
                  refine ⟨373077242894214746991923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 994872647717905991978461 373077242894214746991923)
                  ·
                    rfl

theorem cell21_1634772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_1634772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1634772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1634772 prefixEnd_1634772 := by exact prefixLift 1634772
  have htrace : WordTrace (prefixWord ++ tailWord_1634772) baseStart_1634772 baseEnd_1634772 := by
    simpa [prefixWord, tailWord_1634772, baseEnd_1634772] using wordTrace_append hprefix tailTrace_1634772
  have hstable : (prefixWord ++ tailWord_1634772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634772).length < 2 ^ (prefixWord ++ tailWord_1634772).sum := by decide
  have hdescent : baseEnd_1634772 < baseStart_1634772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634828 : List Nat := [2, 2, 1, 2, 4, 1, 1, 4, 4]
def baseStart_1634828 : Nat := 118140960795 + 1634828 * 2 ^ 59
def prefixEnd_1634828 : Nat := 4983230072969 + 3 ^ 40 * 1634828 * 2
def baseEnd_1634828 : Nat := 373090022857171094058475

theorem tailTrace_1634828 : CollatzResearch.WordTrace tailWord_1634828 prefixEnd_1634828 373090022857171094058475 := by
  unfold tailWord_1634828
  simp only [CollatzResearch.WordTrace]
  refine ⟨29813537860652418619376569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39751383814203224825835425 29813537860652418619376569)
  ·
    refine ⟨22360153395489313964532427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29813537860652418619376569 22360153395489313964532427)
    ·
      refine ⟨33540230093233970946798641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22360153395489313964532427 33540230093233970946798641)
      ·
        refine ⟨25155172569925478210098981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33540230093233970946798641 25155172569925478210098981)
        ·
          refine ⟨4716594856861027164393559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25155172569925478210098981 4716594856861027164393559)
          ·
            refine ⟨7074892285291540746590339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4716594856861027164393559 7074892285291540746590339)
            ·
              refine ⟨10612338427937311119885509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7074892285291540746590339 10612338427937311119885509)
              ·
                refine ⟨1989813455238245834978533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10612338427937311119885509 1989813455238245834978533)
                ·
                  refine ⟨373090022857171094058475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1989813455238245834978533 373090022857171094058475)
                  ·
                    rfl

theorem cell21_1634828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_1634828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1634828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1634828 prefixEnd_1634828 := by exact prefixLift 1634828
  have htrace : WordTrace (prefixWord ++ tailWord_1634828) baseStart_1634828 baseEnd_1634828 := by
    simpa [prefixWord, tailWord_1634828, baseEnd_1634828] using wordTrace_append hprefix tailTrace_1634828
  have hstable : (prefixWord ++ tailWord_1634828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634828).length < 2 ^ (prefixWord ++ tailWord_1634828).sum := by decide
  have hdescent : baseEnd_1634828 < baseStart_1634828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634842 : List Nat := [3, 1, 1, 3, 1, 1, 5, 6]
def baseStart_1634842 : Nat := 118140960795 + 1634842 * 2 ^ 59
def prefixEnd_1634842 : Nat := 4983230072969 + 3 ^ 40 * 1634842 * 2
def baseEnd_1634842 : Nat := 124364405949303393608371

theorem tailTrace_1634842 : CollatzResearch.WordTrace tailWord_1634842 prefixEnd_1634842 124364405949303393608371 := by
  unfold tailWord_1634842
  simp only [CollatzResearch.WordTrace]
  refine ⟨14906896585813529407440695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39751724228836078419841853 14906896585813529407440695)
  ·
    refine ⟨22360344878720294111161043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14906896585813529407440695 22360344878720294111161043)
    ·
      refine ⟨33540517318080441166741565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22360344878720294111161043 33540517318080441166741565)
      ·
        refine ⟨12577693994280165437528087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33540517318080441166741565 12577693994280165437528087)
        ·
          refine ⟨18866540991420248156292131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12577693994280165437528087 18866540991420248156292131)
          ·
            refine ⟨28299811487130372234438197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18866540991420248156292131 28299811487130372234438197)
            ·
              refine ⟨2653107326918472396978581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28299811487130372234438197 2653107326918472396978581)
              ·
                refine ⟨124364405949303393608371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2653107326918472396978581 124364405949303393608371)
                ·
                  rfl

theorem cell21_1634842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 6].length) (baseStart_1634842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1634842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1634842 prefixEnd_1634842 := by exact prefixLift 1634842
  have htrace : WordTrace (prefixWord ++ tailWord_1634842) baseStart_1634842 baseEnd_1634842 := by
    simpa [prefixWord, tailWord_1634842, baseEnd_1634842] using wordTrace_append hprefix tailTrace_1634842
  have hstable : (prefixWord ++ tailWord_1634842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634842).length < 2 ^ (prefixWord ++ tailWord_1634842).sum := by decide
  have hdescent : baseEnd_1634842 < baseStart_1634842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634890 : List Nat := [3, 1, 2, 1, 1, 4, 2, 4, 3]
def baseStart_1634890 : Nat := 118140960795 + 1634890 * 2 ^ 59
def prefixEnd_1634890 : Nat := 4983230072969 + 3 ^ 40 * 1634890 * 2
def baseEnd_1634890 : Nat := 373104172101872764025015

theorem tailTrace_1634890 : CollatzResearch.WordTrace tailWord_1634890 prefixEnd_1634890 373104172101872764025015 := by
  unfold tailWord_1634890
  simp only [CollatzResearch.WordTrace]
  refine ⟨14907334261770055456877531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39752891364720147885006749 14907334261770055456877531)
  ·
    refine ⟨22361001392655083185316297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14907334261770055456877531 22361001392655083185316297)
    ·
      refine ⟨16770751044491312388987223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22361001392655083185316297 16770751044491312388987223)
      ·
        refine ⟨25156126566736968583480835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16770751044491312388987223 25156126566736968583480835)
        ·
          refine ⟨37734189850105452875221253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25156126566736968583480835 37734189850105452875221253)
          ·
            refine ⟨7075160596894772414103985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37734189850105452875221253 7075160596894772414103985)
            ·
              refine ⟨5306370447671079310577989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7075160596894772414103985 5306370447671079310577989)
              ·
                refine ⟨994944458938327370733373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5306370447671079310577989 994944458938327370733373)
                ·
                  refine ⟨373104172101872764025015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 994944458938327370733373 373104172101872764025015)
                  ·
                    rfl

theorem cell21_1634890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4, 3].length) (baseStart_1634890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1634890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1634890 prefixEnd_1634890 := by exact prefixLift 1634890
  have htrace : WordTrace (prefixWord ++ tailWord_1634890) baseStart_1634890 baseEnd_1634890 := by
    simpa [prefixWord, tailWord_1634890, baseEnd_1634890] using wordTrace_append hprefix tailTrace_1634890
  have hstable : (prefixWord ++ tailWord_1634890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634890).length < 2 ^ (prefixWord ++ tailWord_1634890).sum := by decide
  have hdescent : baseEnd_1634890 < baseStart_1634890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634949 : List Nat := [1, 3, 1, 1, 4, 2, 3, 1, 5]
def baseStart_1634949 : Nat := 118140960795 + 1634949 * 2 ^ 59
def prefixEnd_1634949 : Nat := 4983230072969 + 3 ^ 40 * 1634949 * 2
def baseEnd_1634949 : Nat := 373117636705701772541561

theorem tailTrace_1634949 : CollatzResearch.WordTrace tailWord_1634949 prefixEnd_1634949 373117636705701772541561 := by
  unfold tailWord_1634949
  simp only [CollatzResearch.WordTrace]
  refine ⟨59631488953866474903907901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39754325969244316602605267 59631488953866474903907901)
  ·
    refine ⟨22361808357699928088965463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59631488953866474903907901 22361808357699928088965463)
    ·
      refine ⟨33542712536549892133448195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22361808357699928088965463 33542712536549892133448195)
      ·
        refine ⟨50314068804824838200172293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33542712536549892133448195 50314068804824838200172293)
        ·
          refine ⟨9433887900904657162532305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50314068804824838200172293 9433887900904657162532305)
          ·
            refine ⟨7075415925678492871899229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9433887900904657162532305 7075415925678492871899229)
            ·
              refine ⟨2653280972129434826962211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7075415925678492871899229 2653280972129434826962211)
              ·
                refine ⟨3979921458194152240443317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2653280972129434826962211 3979921458194152240443317)
                ·
                  refine ⟨373117636705701772541561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3979921458194152240443317 373117636705701772541561)
                  ·
                    rfl

theorem cell21_1634949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_1634949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1634949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1634949 prefixEnd_1634949 := by exact prefixLift 1634949
  have htrace : WordTrace (prefixWord ++ tailWord_1634949) baseStart_1634949 baseEnd_1634949 := by
    simpa [prefixWord, tailWord_1634949, baseEnd_1634949] using wordTrace_append hprefix tailTrace_1634949
  have hstable : (prefixWord ++ tailWord_1634949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634949).length < 2 ^ (prefixWord ++ tailWord_1634949).sum := by decide
  have hdescent : baseEnd_1634949 < baseStart_1634949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634963 : List Nat := [1, 1, 1, 2, 1, 2, 2, 7, 4]
def baseStart_1634963 : Nat := 118140960795 + 1634963 * 2 ^ 59
def prefixEnd_1634963 : Nat := 4983230072969 + 3 ^ 40 * 1634963 * 2
def baseEnd_1634963 : Nat := 373120831696440859308199

theorem tailTrace_1634963 : CollatzResearch.WordTrace tailWord_1634963 prefixEnd_1634963 373120831696440859308199 := by
  unfold tailWord_1634963
  simp only [CollatzResearch.WordTrace]
  refine ⟨59631999575815755294917543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39754666383877170196611695 59631999575815755294917543)
  ·
    refine ⟨89447999363723632942376315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59631999575815755294917543 89447999363723632942376315)
    ·
      refine ⟨134171999045585449413564473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89447999363723632942376315 134171999045585449413564473)
      ·
        refine ⟨100628999284189087060173355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134171999045585449413564473 100628999284189087060173355)
        ·
          refine ⟨150943498926283630590260033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100628999284189087060173355 150943498926283630590260033)
          ·
            refine ⟨113207624194712722942695025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150943498926283630590260033 113207624194712722942695025)
            ·
              refine ⟨84905718146034542207021269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113207624194712722942695025 84905718146034542207021269)
              ·
                refine ⟨1989977769047684582977061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 84905718146034542207021269 1989977769047684582977061)
                ·
                  refine ⟨373120831696440859308199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1989977769047684582977061 373120831696440859308199)
                  ·
                    rfl

theorem cell21_1634963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 4].length) (baseStart_1634963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1634963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1634963 prefixEnd_1634963 := by exact prefixLift 1634963
  have htrace : WordTrace (prefixWord ++ tailWord_1634963) baseStart_1634963 baseEnd_1634963 := by
    simpa [prefixWord, tailWord_1634963, baseEnd_1634963] using wordTrace_append hprefix tailTrace_1634963
  have hstable : (prefixWord ++ tailWord_1634963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634963).length < 2 ^ (prefixWord ++ tailWord_1634963).sum := by decide
  have hdescent : baseEnd_1634963 < baseStart_1634963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634997 : List Nat := [1, 3, 3, 3, 1, 2, 2, 2, 4]
def baseStart_1634997 : Nat := 118140960795 + 1634997 * 2 ^ 59
def prefixEnd_1634997 : Nat := 4983230072969 + 3 ^ 40 * 1634997 * 2
def baseEnd_1634997 : Nat := 373128590959664355741463

theorem tailTrace_1634997 : CollatzResearch.WordTrace tailWord_1634997 prefixEnd_1634997 373128590959664355741463 := by
  unfold tailWord_1634997
  simp only [CollatzResearch.WordTrace]
  refine ⟨59633239657692579101655245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39755493105128386067770163 59633239657692579101655245)
  ·
    refine ⟨22362464871634717163120717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59633239657692579101655245 22362464871634717163120717)
    ·
      refine ⟨8385924326863018936170269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22362464871634717163120717 8385924326863018936170269)
      ·
        refine ⟨3144721622573632101063851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8385924326863018936170269 3144721622573632101063851)
        ·
          refine ⟨4717082433860448151595777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3144721622573632101063851 4717082433860448151595777)
          ·
            refine ⟨3537811825395336113696833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4717082433860448151595777 3537811825395336113696833)
            ·
              refine ⟨2653358869046502085272625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3537811825395336113696833 2653358869046502085272625)
              ·
                refine ⟨1990019151784876563954469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2653358869046502085272625 1990019151784876563954469)
                ·
                  refine ⟨373128590959664355741463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1990019151784876563954469 373128590959664355741463)
                  ·
                    rfl

theorem cell21_1634997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_1634997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1634997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1634997 prefixEnd_1634997 := by exact prefixLift 1634997
  have htrace : WordTrace (prefixWord ++ tailWord_1634997) baseStart_1634997 baseEnd_1634997 := by
    simpa [prefixWord, tailWord_1634997, baseEnd_1634997] using wordTrace_append hprefix tailTrace_1634997
  have hstable : (prefixWord ++ tailWord_1634997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634997).length < 2 ^ (prefixWord ++ tailWord_1634997).sum := by decide
  have hdescent : baseEnd_1634997 < baseStart_1634997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635028 : List Nat := [2, 4, 1, 3, 2, 1, 3, 5]
def baseStart_1635028 : Nat := 118140960795 + 1635028 * 2 ^ 59
def prefixEnd_1635028 : Nat := 4983230072969 + 3 ^ 40 * 1635028 * 2
def baseEnd_1635028 : Nat := 124378555194005063574911

theorem tailTrace_1635028 : CollatzResearch.WordTrace tailWord_1635028 prefixEnd_1635028 124378555194005063574911 := by
  unfold tailWord_1635028
  simp only [CollatzResearch.WordTrace]
  refine ⟨29817185160290135698016869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39756246880386847597355825 29817185160290135698016869)
  ·
    refine ⟨5590722217554400443378163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29817185160290135698016869 5590722217554400443378163)
    ·
      refine ⟨8386083326331600665067245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5590722217554400443378163 8386083326331600665067245)
      ·
        refine ⟨3144781247374350249400217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8386083326331600665067245 3144781247374350249400217)
        ·
          refine ⟨2358585935530762687050163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3144781247374350249400217 2358585935530762687050163)
          ·
            refine ⟨3537878903296144030575245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2358585935530762687050163 3537878903296144030575245)
            ·
              refine ⟨1326704588736054011465717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3537878903296144030575245 1326704588736054011465717)
              ·
                refine ⟨124378555194005063574911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1326704588736054011465717 124378555194005063574911)
                ·
                  rfl

theorem cell21_1635028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 5].length) (baseStart_1635028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1635028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1635028 prefixEnd_1635028 := by exact prefixLift 1635028
  have htrace : WordTrace (prefixWord ++ tailWord_1635028) baseStart_1635028 baseEnd_1635028 := by
    simpa [prefixWord, tailWord_1635028, baseEnd_1635028] using wordTrace_append hprefix tailTrace_1635028
  have hstable : (prefixWord ++ tailWord_1635028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635028).length < 2 ^ (prefixWord ++ tailWord_1635028).sum := by decide
  have hdescent : baseEnd_1635028 < baseStart_1635028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635118 : List Nat := [4, 1, 3, 2, 1, 1, 3, 1, 5]
def baseStart_1635118 : Nat := 118140960795 + 1635118 * 2 ^ 59
def prefixEnd_1635118 : Nat := 4983230072969 + 3 ^ 40 * 1635118 * 2
def baseEnd_1635118 : Nat := 373156204808195034224549

theorem tailTrace_1635118 : CollatzResearch.WordTrace tailWord_1635118 prefixEnd_1635118 373156204808195034224549 := by
  unfold tailWord_1635118
  simp only [CollatzResearch.WordTrace]
  refine ⟨7454706611281777095851251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39758435260169477844540005 7454706611281777095851251)
  ·
    refine ⟨11182059916922665643776877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7454706611281777095851251 11182059916922665643776877)
    ·
      refine ⟨4193272468845999616416329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11182059916922665643776877 4193272468845999616416329)
      ·
        refine ⟨3144954351634499712312247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4193272468845999616416329 3144954351634499712312247)
        ·
          refine ⟨4717431527451749568468371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3144954351634499712312247 4717431527451749568468371)
          ·
            refine ⟨7076147291177624352702557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4717431527451749568468371 7076147291177624352702557)
            ·
              refine ⟨2653555234191609132263459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7076147291177624352702557 2653555234191609132263459)
              ·
                refine ⟨3980332851287413698395189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2653555234191609132263459 3980332851287413698395189)
                ·
                  refine ⟨373156204808195034224549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3980332851287413698395189 373156204808195034224549)
                  ·
                    rfl

theorem cell21_1635118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_1635118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1635118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1635118 prefixEnd_1635118 := by exact prefixLift 1635118
  have htrace : WordTrace (prefixWord ++ tailWord_1635118) baseStart_1635118 baseEnd_1635118 := by
    simpa [prefixWord, tailWord_1635118, baseEnd_1635118] using wordTrace_append hprefix tailTrace_1635118
  have hstable : (prefixWord ++ tailWord_1635118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635118).length < 2 ^ (prefixWord ++ tailWord_1635118).sum := by decide
  have hdescent : baseEnd_1635118 < baseStart_1635118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635301 : List Nat := [1, 3, 1, 6, 1, 1, 1, 3, 4]
def baseStart_1635301 : Nat := 118140960795 + 1635301 * 2 ^ 59
def prefixEnd_1635301 : Nat := 4983230072969 + 3 ^ 40 * 1635301 * 2
def baseEnd_1635301 : Nat := 373197967901427382674175

theorem tailTrace_1635301 : CollatzResearch.WordTrace tailWord_1635301 prefixEnd_1635301 373197967901427382674175 := by
  unfold tailWord_1635301
  simp only [CollatzResearch.WordTrace]
  refine ⟨59644327448591239020721757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39762884965727492680481171 59644327448591239020721757)
  ·
    refine ⟨22366622793221714632770659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59644327448591239020721757 22366622793221714632770659)
    ·
      refine ⟨33549934189832571949155989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22366622793221714632770659 33549934189832571949155989)
      ·
        refine ⟨1572653165148401810116687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33549934189832571949155989 1572653165148401810116687)
        ·
          refine ⟨2358979747722602715175031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1572653165148401810116687 2358979747722602715175031)
          ·
            refine ⟨3538469621583904072762547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2358979747722602715175031 3538469621583904072762547)
            ·
              refine ⟨5307704432375856109143821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3538469621583904072762547 5307704432375856109143821)
              ·
                refine ⟨1990389162140946040928933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5307704432375856109143821 1990389162140946040928933)
                ·
                  refine ⟨373197967901427382674175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1990389162140946040928933 373197967901427382674175)
                  ·
                    rfl

theorem cell21_1635301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_1635301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1635301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1635301 prefixEnd_1635301 := by exact prefixLift 1635301
  have htrace : WordTrace (prefixWord ++ tailWord_1635301) baseStart_1635301 baseEnd_1635301 := by
    simpa [prefixWord, tailWord_1635301, baseEnd_1635301] using wordTrace_append hprefix tailTrace_1635301
  have hstable : (prefixWord ++ tailWord_1635301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635301).length < 2 ^ (prefixWord ++ tailWord_1635301).sum := by decide
  have hdescent : baseEnd_1635301 < baseStart_1635301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635405 : List Nat := [1, 6, 1, 1, 1, 2, 1, 3, 5]
def baseStart_1635405 : Nat := 118140960795 + 1635405 * 2 ^ 59
def prefixEnd_1635405 : Nat := 4983230072969 + 3 ^ 40 * 1635405 * 2
def baseEnd_1635405 : Nat := 373221702118346312940629

theorem tailTrace_1635405 : CollatzResearch.WordTrace tailWord_1635405 prefixEnd_1635405 373221702118346312940629 := by
  unfold tailWord_1635405
  simp only [CollatzResearch.WordTrace]
  refine ⟨59648120640214464782507669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39765413760142976521671779 59648120640214464782507669)
  ·
    refine ⟨2796005655010053036680047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 59648120640214464782507669 2796005655010053036680047)
    ·
      refine ⟨4194008482515079555020071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2796005655010053036680047 4194008482515079555020071)
      ·
        refine ⟨6291012723772619332530107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4194008482515079555020071 6291012723772619332530107)
        ·
          refine ⟨9436519085658928998795161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6291012723772619332530107 9436519085658928998795161)
          ·
            refine ⟨7077389314244196749096371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9436519085658928998795161 7077389314244196749096371)
            ·
              refine ⟨10616083971366295123644557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7077389314244196749096371 10616083971366295123644557)
              ·
                refine ⟨3981031489262360671366709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10616083971366295123644557 3981031489262360671366709)
                ·
                  refine ⟨373221702118346312940629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3981031489262360671366709 373221702118346312940629)
                  ·
                    rfl

theorem cell21_1635405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_1635405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1635405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1635405 prefixEnd_1635405 := by exact prefixLift 1635405
  have htrace : WordTrace (prefixWord ++ tailWord_1635405) baseStart_1635405 baseEnd_1635405 := by
    simpa [prefixWord, tailWord_1635405, baseEnd_1635405] using wordTrace_append hprefix tailTrace_1635405
  have hstable : (prefixWord ++ tailWord_1635405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635405).length < 2 ^ (prefixWord ++ tailWord_1635405).sum := by decide
  have hdescent : baseEnd_1635405 < baseStart_1635405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635433 : List Nat := [1, 2, 1, 1, 1, 7, 1, 7]
def baseStart_1635433 : Nat := 118140960795 + 1635433 * 2 ^ 59
def prefixEnd_1635433 : Nat := 4983230072969 + 3 ^ 40 * 1635433 * 2
def baseEnd_1635433 : Nat := 124409364033274828824635

theorem tailTrace_1635433 : CollatzResearch.WordTrace tailWord_1635433 prefixEnd_1635433 124409364033274828824635 := by
  unfold tailWord_1635433
  simp only [CollatzResearch.WordTrace]
  refine ⟨59649141884113025564526953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39766094589408683709684635 59649141884113025564526953)
  ·
    refine ⟨44736856413084769173395215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59649141884113025564526953 44736856413084769173395215)
    ·
      refine ⟨67105284619627153760092823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44736856413084769173395215 67105284619627153760092823)
      ·
        refine ⟨100657926929440730640139235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67105284619627153760092823 100657926929440730640139235)
        ·
          refine ⟨150986890394161095960208853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100657926929440730640139235 150986890394161095960208853)
          ·
            refine ⟨3538755243613150686567395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 150986890394161095960208853 3538755243613150686567395)
            ·
              refine ⟨5308132865419726029851093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3538755243613150686567395 5308132865419726029851093)
              ·
                refine ⟨124409364033274828824635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5308132865419726029851093 124409364033274828824635)
                ·
                  rfl

theorem cell21_1635433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 7].length) (baseStart_1635433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1635433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1635433 prefixEnd_1635433 := by exact prefixLift 1635433
  have htrace : WordTrace (prefixWord ++ tailWord_1635433) baseStart_1635433 baseEnd_1635433 := by
    simpa [prefixWord, tailWord_1635433, baseEnd_1635433] using wordTrace_append hprefix tailTrace_1635433
  have hstable : (prefixWord ++ tailWord_1635433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635433).length < 2 ^ (prefixWord ++ tailWord_1635433).sum := by decide
  have hdescent : baseEnd_1635433 < baseStart_1635433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635571 : List Nat := [1, 1, 1, 2, 2, 5, 3, 2, 4]
def baseStart_1635571 : Nat := 118140960795 + 1635571 * 2 ^ 59
def prefixEnd_1635571 : Nat := 4983230072969 + 3 ^ 40 * 1635571 * 2
def baseEnd_1635571 : Nat := 373259585579966913173623

theorem tailTrace_1635571 : CollatzResearch.WordTrace tailWord_1635571 prefixEnd_1635571 373259585579966913173623 := by
  unfold tailWord_1635571
  simp only [CollatzResearch.WordTrace]
  refine ⟨59654175157613075133050567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39769450105075383422033711 59654175157613075133050567)
  ·
    refine ⟨89481262736419612699575851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59654175157613075133050567 89481262736419612699575851)
    ·
      refine ⟨134221894104629419049363777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89481262736419612699575851 134221894104629419049363777)
      ·
        refine ⟨100666420578472064287022833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134221894104629419049363777 100666420578472064287022833)
        ·
          refine ⟨75499815433854048215267125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100666420578472064287022833 75499815433854048215267125)
          ·
            refine ⟨7078107696923817020181293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75499815433854048215267125 7078107696923817020181293)
            ·
              refine ⟨2654290386346431382567985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7078107696923817020181293 2654290386346431382567985)
              ·
                refine ⟨1990717789759823536925989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2654290386346431382567985 1990717789759823536925989)
                ·
                  refine ⟨373259585579966913173623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1990717789759823536925989 373259585579966913173623)
                  ·
                    rfl

theorem cell21_1635571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 4].length) (baseStart_1635571 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1635571 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1635571 prefixEnd_1635571 := by exact prefixLift 1635571
  have htrace : WordTrace (prefixWord ++ tailWord_1635571) baseStart_1635571 baseEnd_1635571 := by
    simpa [prefixWord, tailWord_1635571, baseEnd_1635571] using wordTrace_append hprefix tailTrace_1635571
  have hstable : (prefixWord ++ tailWord_1635571).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635571).length < 2 ^ (prefixWord ++ tailWord_1635571).sum := by decide
  have hdescent : baseEnd_1635571 < baseStart_1635571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635633 : List Nat := [1, 2, 2, 3, 3, 3, 1, 1, 5]
def baseStart_1635633 : Nat := 118140960795 + 1635633 * 2 ^ 59
def prefixEnd_1635633 : Nat := 4983230072969 + 3 ^ 40 * 1635633 * 2
def baseEnd_1635633 : Nat := 373273734824668583140163

theorem tailTrace_1635633 : CollatzResearch.WordTrace tailWord_1635633 prefixEnd_1635633 373273734824668583140163 := by
  unfold tailWord_1635633
  simp only [CollatzResearch.WordTrace]
  refine ⟨59656436483388459721807553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39770957655592306481205035 59656436483388459721807553)
  ·
    refine ⟨44742327362541344791355665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59656436483388459721807553 44742327362541344791355665)
    ·
      refine ⟨33556745521906008593516749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44742327362541344791355665 33556745521906008593516749)
      ·
        refine ⟨12583779570714753222568781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33556745521906008593516749 12583779570714753222568781)
        ·
          refine ⟨4718917339018032458463293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12583779570714753222568781 4718917339018032458463293)
          ·
            refine ⟨1769594002131762171923735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4718917339018032458463293 1769594002131762171923735)
            ·
              refine ⟨2654391003197643257885603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1769594002131762171923735 2654391003197643257885603)
              ·
                refine ⟨3981586504796464886828405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2654391003197643257885603 3981586504796464886828405)
                ·
                  refine ⟨373273734824668583140163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3981586504796464886828405 373273734824668583140163)
                  ·
                    rfl

theorem cell21_1635633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 5].length) (baseStart_1635633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1635633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1635633 prefixEnd_1635633 := by exact prefixLift 1635633
  have htrace : WordTrace (prefixWord ++ tailWord_1635633) baseStart_1635633 baseEnd_1635633 := by
    simpa [prefixWord, tailWord_1635633, baseEnd_1635633] using wordTrace_append hprefix tailTrace_1635633
  have hstable : (prefixWord ++ tailWord_1635633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635633).length < 2 ^ (prefixWord ++ tailWord_1635633).sum := by decide
  have hdescent : baseEnd_1635633 < baseStart_1635633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635647 : List Nat := [1, 1, 2, 2, 4, 3, 1, 3, 4]
def baseStart_1635647 : Nat := 118140960795 + 1635647 * 2 ^ 59
def prefixEnd_1635647 : Nat := 4983230072969 + 3 ^ 40 * 1635647 * 2
def baseEnd_1635647 : Nat := 373276929815407669906801

theorem tailTrace_1635647 : CollatzResearch.WordTrace tailWord_1635647 prefixEnd_1635647 373276929815407669906801 := by
  unfold tailWord_1635647
  simp only [CollatzResearch.WordTrace]
  refine ⟨59656947105337740112817195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39771298070225160075211463 59656947105337740112817195)
  ·
    refine ⟨89485420658006610169225793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59656947105337740112817195 89485420658006610169225793)
    ·
      refine ⟨67114065493504957626919345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89485420658006610169225793 67114065493504957626919345)
      ·
        refine ⟨50335549120128718220189509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67114065493504957626919345 50335549120128718220189509)
        ·
          refine ⟨9437915460024134666285533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50335549120128718220189509 9437915460024134666285533)
          ·
            refine ⟨3539218297509050499857075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9437915460024134666285533 3539218297509050499857075)
            ·
              refine ⟨5308827446263575749785613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3539218297509050499857075 5308827446263575749785613)
              ·
                refine ⟨1990810292348840906169605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5308827446263575749785613 1990810292348840906169605)
                ·
                  refine ⟨373276929815407669906801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1990810292348840906169605 373276929815407669906801)
                  ·
                    rfl

theorem cell21_1635647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 4].length) (baseStart_1635647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1635647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1635647 prefixEnd_1635647 := by exact prefixLift 1635647
  have htrace : WordTrace (prefixWord ++ tailWord_1635647) baseStart_1635647 baseEnd_1635647 := by
    simpa [prefixWord, tailWord_1635647, baseEnd_1635647] using wordTrace_append hprefix tailTrace_1635647
  have hstable : (prefixWord ++ tailWord_1635647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635647).length < 2 ^ (prefixWord ++ tailWord_1635647).sum := by decide
  have hdescent : baseEnd_1635647 < baseStart_1635647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635740 : List Nat := [2, 2, 3, 4, 1, 1, 1, 1, 6]
def baseStart_1635740 : Nat := 118140960795 + 1635740 * 2 ^ 59
def prefixEnd_1635740 : Nat := 4983230072969 + 3 ^ 40 * 1635740 * 2
def baseEnd_1635740 : Nat := 373298153682460174856611

theorem tailTrace_1635740 : CollatzResearch.WordTrace tailWord_1635740 prefixEnd_1635740 373298153682460174856611 := by
  unfold tailWord_1635740
  simp only [CollatzResearch.WordTrace]
  refine ⟨29830169547000408497976337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39773559396000544663968449 29830169547000408497976337)
  ·
    refine ⟨22372627160250306373482253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29830169547000408497976337 22372627160250306373482253)
    ·
      refine ⟨8389735185093864890055845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22372627160250306373482253 8389735185093864890055845)
      ·
        refine ⟨1573075347205099666885471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8389735185093864890055845 1573075347205099666885471)
        ·
          refine ⟨2359613020807649500328207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1573075347205099666885471 2359613020807649500328207)
          ·
            refine ⟨3539419531211474250492311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2359613020807649500328207 3539419531211474250492311)
            ·
              refine ⟨5309129296817211375738467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3539419531211474250492311 5309129296817211375738467)
              ·
                refine ⟨7963693945225817063607701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5309129296817211375738467 7963693945225817063607701)
                ·
                  refine ⟨373298153682460174856611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7963693945225817063607701 373298153682460174856611)
                  ·
                    rfl

theorem cell21_1635740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_1635740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1635740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1635740 prefixEnd_1635740 := by exact prefixLift 1635740
  have htrace : WordTrace (prefixWord ++ tailWord_1635740) baseStart_1635740 baseEnd_1635740 := by
    simpa [prefixWord, tailWord_1635740, baseEnd_1635740] using wordTrace_append hprefix tailTrace_1635740
  have hstable : (prefixWord ++ tailWord_1635740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635740).length < 2 ^ (prefixWord ++ tailWord_1635740).sum := by decide
  have hdescent : baseEnd_1635740 < baseStart_1635740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635757 : List Nat := [1, 5, 2, 2, 1, 2, 3, 1, 4]
def baseStart_1635757 : Nat := 118140960795 + 1635757 * 2 ^ 59
def prefixEnd_1635757 : Nat := 4983230072969 + 3 ^ 40 * 1635757 * 2
def baseEnd_1635757 : Nat := 373302033314071923073243

theorem tailTrace_1635757 : CollatzResearch.WordTrace tailWord_1635757 prefixEnd_1635757 373302033314071923073243 := by
  unfold tailWord_1635757
  simp only [CollatzResearch.WordTrace]
  refine ⟨59660959134939228899321525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39773972756626152599547683 59660959134939228899321525)
  ·
    refine ⟨5593214918900552709311393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59660959134939228899321525 5593214918900552709311393)
    ·
      refine ⟨4194911189175414531983545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5593214918900552709311393 4194911189175414531983545)
      ·
        refine ⟨3146183391881560898987659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4194911189175414531983545 3146183391881560898987659)
        ·
          refine ⟨4719275087822341348481489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3146183391881560898987659 4719275087822341348481489)
          ·
            refine ⟨3539456315866756011361117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4719275087822341348481489 3539456315866756011361117)
            ·
              refine ⟨1327296118450033504260419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3539456315866756011361117 1327296118450033504260419)
              ·
                refine ⟨1990944177675050256390629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1327296118450033504260419 1990944177675050256390629)
                ·
                  refine ⟨373302033314071923073243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1990944177675050256390629 373302033314071923073243)
                  ·
                    rfl

theorem cell21_1635757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_1635757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1635757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1635757 prefixEnd_1635757 := by exact prefixLift 1635757
  have htrace : WordTrace (prefixWord ++ tailWord_1635757) baseStart_1635757 baseEnd_1635757 := by
    simpa [prefixWord, tailWord_1635757, baseEnd_1635757] using wordTrace_append hprefix tailTrace_1635757
  have hstable : (prefixWord ++ tailWord_1635757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635757).length < 2 ^ (prefixWord ++ tailWord_1635757).sum := by decide
  have hdescent : baseEnd_1635757 < baseStart_1635757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635802 : List Nat := [3, 1, 1, 2, 3, 3, 3, 2, 3]
def baseStart_1635802 : Nat := 118140960795 + 1635802 * 2 ^ 59
def prefixEnd_1635802 : Nat := 4983230072969 + 3 ^ 40 * 1635802 * 2
def baseEnd_1635802 : Nat := 373312302927161844823151

theorem tailTrace_1635802 : CollatzResearch.WordTrace tailWord_1635802 prefixEnd_1635802 373312302927161844823151 := by
  unfold tailWord_1635802
  simp only [CollatzResearch.WordTrace]
  refine ⟨14915650104944050396177415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39775066946517467723139773 14915650104944050396177415)
  ·
    refine ⟨22373475157416075594266123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14915650104944050396177415 22373475157416075594266123)
    ·
      refine ⟨33560212736124113391399185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22373475157416075594266123 33560212736124113391399185)
      ·
        refine ⟨25170159552093085043549389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33560212736124113391399185 25170159552093085043549389)
        ·
          refine ⟨9438809832034906891331021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25170159552093085043549389 9438809832034906891331021)
          ·
            refine ⟨3539553687013090084249133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9438809832034906891331021 3539553687013090084249133)
            ·
              refine ⟨1327332632629908781593425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3539553687013090084249133 1327332632629908781593425)
              ·
                refine ⟨995499474472431586195069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1327332632629908781593425 995499474472431586195069)
                ·
                  refine ⟨373312302927161844823151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 995499474472431586195069 373312302927161844823151)
                  ·
                    rfl

theorem cell21_1635802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2, 3].length) (baseStart_1635802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1635802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1635802 prefixEnd_1635802 := by exact prefixLift 1635802
  have htrace : WordTrace (prefixWord ++ tailWord_1635802) baseStart_1635802 baseEnd_1635802 := by
    simpa [prefixWord, tailWord_1635802, baseEnd_1635802] using wordTrace_append hprefix tailTrace_1635802
  have hstable : (prefixWord ++ tailWord_1635802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635802).length < 2 ^ (prefixWord ++ tailWord_1635802).sum := by decide
  have hdescent : baseEnd_1635802 < baseStart_1635802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635813 : List Nat := [1, 3, 1, 5, 1, 1, 1, 8]
def baseStart_1635813 : Nat := 118140960795 + 1635813 * 2 ^ 59
def prefixEnd_1635813 : Nat := 4983230072969 + 3 ^ 40 * 1635813 * 2
def baseEnd_1635813 : Nat := 124438271092342756713265

theorem tailTrace_1635813 : CollatzResearch.WordTrace tailWord_1635813 prefixEnd_1635813 124438271092342756713265 := by
  unfold tailWord_1635813
  simp only [CollatzResearch.WordTrace]
  refine ⟨59663001622736350463360093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39775334415157566975573395 59663001622736350463360093)
  ·
    refine ⟨22373625608526131423760035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59663001622736350463360093 22373625608526131423760035)
    ·
      refine ⟨33560438412789197135640053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22373625608526131423760035 33560438412789197135640053)
      ·
        refine ⟨3146291101198987231466255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33560438412789197135640053 3146291101198987231466255)
        ·
          refine ⟨4719436651798480847199383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3146291101198987231466255 4719436651798480847199383)
          ·
            refine ⟨7079154977697721270799075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4719436651798480847199383 7079154977697721270799075)
            ·
              refine ⟨10618732466546581906198613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7079154977697721270799075 10618732466546581906198613)
              ·
                refine ⟨124438271092342756713265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10618732466546581906198613 124438271092342756713265)
                ·
                  rfl

theorem cell21_1635813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 8].length) (baseStart_1635813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1635813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1635813 prefixEnd_1635813 := by exact prefixLift 1635813
  have htrace : WordTrace (prefixWord ++ tailWord_1635813) baseStart_1635813 baseEnd_1635813 := by
    simpa [prefixWord, tailWord_1635813, baseEnd_1635813] using wordTrace_append hprefix tailTrace_1635813
  have hstable : (prefixWord ++ tailWord_1635813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635813).length < 2 ^ (prefixWord ++ tailWord_1635813).sum := by decide
  have hdescent : baseEnd_1635813 < baseStart_1635813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635853 : List Nat := [1, 7, 1, 1, 2, 2, 2, 2, 3]
def baseStart_1635853 : Nat := 118140960795 + 1635853 * 2 ^ 59
def prefixEnd_1635853 : Nat := 4983230072969 + 3 ^ 40 * 1635853 * 2
def baseEnd_1635853 : Nat := 373323941821997089473047

theorem tailTrace_1635853 : CollatzResearch.WordTrace tailWord_1635853 prefixEnd_1635853 373323941821997089473047 := by
  unfold tailWord_1635853
  simp only [CollatzResearch.WordTrace]
  refine ⟨59664460542591437294816213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39776307028394291529877475 59664460542591437294816213)
  ·
    refine ⟨1398385793966986811597255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 59664460542591437294816213 1398385793966986811597255)
    ·
      refine ⟨2097578690950480217395883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1398385793966986811597255 2097578690950480217395883)
      ·
        refine ⟨3146368036425720326093825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2097578690950480217395883 3146368036425720326093825)
        ·
          refine ⟨2359776027319290244570369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3146368036425720326093825 2359776027319290244570369)
          ·
            refine ⟨1769832020489467683427777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2359776027319290244570369 1769832020489467683427777)
            ·
              refine ⟨1327374015367100762570833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1769832020489467683427777 1327374015367100762570833)
              ·
                refine ⟨995530511525325571928125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1327374015367100762570833 995530511525325571928125)
                ·
                  refine ⟨373323941821997089473047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 995530511525325571928125 373323941821997089473047)
                  ·
                    rfl

theorem cell21_1635853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_1635853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1635853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1635853 prefixEnd_1635853 := by exact prefixLift 1635853
  have htrace : WordTrace (prefixWord ++ tailWord_1635853) baseStart_1635853 baseEnd_1635853 := by
    simpa [prefixWord, tailWord_1635853, baseEnd_1635853] using wordTrace_append hprefix tailTrace_1635853
  have hstable : (prefixWord ++ tailWord_1635853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635853).length < 2 ^ (prefixWord ++ tailWord_1635853).sum := by decide
  have hdescent : baseEnd_1635853 < baseStart_1635853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635861 : List Nat := [1, 3, 2, 1, 3, 3, 1, 4, 3]
def baseStart_1635861 : Nat := 118140960795 + 1635861 * 2 ^ 59
def prefixEnd_1635861 : Nat := 4983230072969 + 3 ^ 40 * 1635861 * 2
def baseEnd_1635861 : Nat := 373325767530990853339697

theorem tailTrace_1635861 : CollatzResearch.WordTrace tailWord_1635861 prefixEnd_1635861 373325767530990853339697 := by
  unfold tailWord_1635861
  simp only [CollatzResearch.WordTrace]
  refine ⟨59664752326562454661107437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39776501551041636440738291 59664752326562454661107437)
  ·
    refine ⟨22374282122460920497915289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59664752326562454661107437 22374282122460920497915289)
    ·
      refine ⟨16780711591845690373436467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22374282122460920497915289 16780711591845690373436467)
      ·
        refine ⟨25171067387768535560154701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16780711591845690373436467 25171067387768535560154701)
        ·
          refine ⟨9439150270413200835058013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25171067387768535560154701 9439150270413200835058013)
          ·
            refine ⟨3539681351404950313146755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9439150270413200835058013 3539681351404950313146755)
            ·
              refine ⟨5309522027107425469720133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3539681351404950313146755 5309522027107425469720133)
              ·
                refine ⟨995535380082642275572525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5309522027107425469720133 995535380082642275572525)
                ·
                  refine ⟨373325767530990853339697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 995535380082642275572525 373325767530990853339697)
                  ·
                    rfl

theorem cell21_1635861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4, 3].length) (baseStart_1635861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1635861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1635861 prefixEnd_1635861 := by exact prefixLift 1635861
  have htrace : WordTrace (prefixWord ++ tailWord_1635861) baseStart_1635861 baseEnd_1635861 := by
    simpa [prefixWord, tailWord_1635861, baseEnd_1635861] using wordTrace_append hprefix tailTrace_1635861
  have hstable : (prefixWord ++ tailWord_1635861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635861).length < 2 ^ (prefixWord ++ tailWord_1635861).sum := by decide
  have hdescent : baseEnd_1635861 < baseStart_1635861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635920 : List Nat := [2, 1, 1, 1, 1, 3, 3, 6, 3]
def baseStart_1635920 : Nat := 118140960795 + 1635920 * 2 ^ 59
def prefixEnd_1635920 : Nat := 4983230072969 + 3 ^ 40 * 1635920 * 2
def baseEnd_1635920 : Nat := 373339232134819861856243

theorem tailTrace_1635920 : CollatzResearch.WordTrace tailWord_1635920 prefixEnd_1635920 373339232134819861856243 := by
  unfold tailWord_1635920
  simp only [CollatzResearch.WordTrace]
  refine ⟨29833452116674353868752607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39777936155565805158336809 29833452116674353868752607)
  ·
    refine ⟨44750178175011530803128911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29833452116674353868752607 44750178175011530803128911)
    ·
      refine ⟨67125267262517296204693367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44750178175011530803128911 67125267262517296204693367)
      ·
        refine ⟨100687900893775944307040051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67125267262517296204693367 100687900893775944307040051)
        ·
          refine ⟨151031851340663916460560077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100687900893775944307040051 151031851340663916460560077)
          ·
            refine ⟨56636944252748968672710029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151031851340663916460560077 56636944252748968672710029)
            ·
              refine ⟨21238854094780863252266261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56636944252748968672710029 21238854094780863252266261)
              ·
                refine ⟨995571285692852964949981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21238854094780863252266261 995571285692852964949981)
                ·
                  refine ⟨373339232134819861856243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 995571285692852964949981 373339232134819861856243)
                  ·
                    rfl

theorem cell21_1635920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6, 3].length) (baseStart_1635920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1635920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1635920 prefixEnd_1635920 := by exact prefixLift 1635920
  have htrace : WordTrace (prefixWord ++ tailWord_1635920) baseStart_1635920 baseEnd_1635920 := by
    simpa [prefixWord, tailWord_1635920, baseEnd_1635920] using wordTrace_append hprefix tailTrace_1635920
  have hstable : (prefixWord ++ tailWord_1635920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635920).length < 2 ^ (prefixWord ++ tailWord_1635920).sum := by decide
  have hdescent : baseEnd_1635920 < baseStart_1635920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635954 : List Nat := [3, 2, 1, 2, 3, 3, 1, 3, 3]
def baseStart_1635954 : Nat := 118140960795 + 1635954 * 2 ^ 59
def prefixEnd_1635954 : Nat := 4983230072969 + 3 ^ 40 * 1635954 * 2
def baseEnd_1635954 : Nat := 373346991398043358289507

theorem tailTrace_1635954 : CollatzResearch.WordTrace tailWord_1635954 prefixEnd_1635954 373346991398043358289507 := by
  unfold tailWord_1635954
  simp only [CollatzResearch.WordTrace]
  refine ⟨14917036078806382886060729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39778762876817021029495277 14917036078806382886060729)
  ·
    refine ⟨11187777059104787164545547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14917036078806382886060729 11187777059104787164545547)
    ·
      refine ⟨16781665588657180746818321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11187777059104787164545547 16781665588657180746818321)
      ·
        refine ⟨12586249191492885560113741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16781665588657180746818321 12586249191492885560113741)
        ·
          refine ⟨4719843446809832085042653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12586249191492885560113741 4719843446809832085042653)
          ·
            refine ⟨1769941292553687031890995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4719843446809832085042653 1769941292553687031890995)
            ·
              refine ⟨2654911938830530547836493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1769941292553687031890995 2654911938830530547836493)
              ·
                refine ⟨995591977061448955438685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2654911938830530547836493 995591977061448955438685)
                ·
                  refine ⟨373346991398043358289507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 995591977061448955438685 373346991398043358289507)
                  ·
                    rfl

theorem cell21_1635954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_1635954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1635954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1635954 prefixEnd_1635954 := by exact prefixLift 1635954
  have htrace : WordTrace (prefixWord ++ tailWord_1635954) baseStart_1635954 baseEnd_1635954 := by
    simpa [prefixWord, tailWord_1635954, baseEnd_1635954] using wordTrace_append hprefix tailTrace_1635954
  have hstable : (prefixWord ++ tailWord_1635954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635954).length < 2 ^ (prefixWord ++ tailWord_1635954).sum := by decide
  have hdescent : baseEnd_1635954 < baseStart_1635954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635965 : List Nat := [1, 4, 1, 1, 4, 3, 7]
def baseStart_1635965 : Nat := 118140960795 + 1635965 * 2 ^ 59
def prefixEnd_1635965 : Nat := 4983230072969 + 3 ^ 40 * 1635965 * 2
def baseEnd_1635965 : Nat := 41483277971989975956239

theorem tailTrace_1635965 : CollatzResearch.WordTrace tailWord_1635965 prefixEnd_1635965 41483277971989975956239 := by
  unfold tailWord_1635965
  simp only [CollatzResearch.WordTrace]
  refine ⟨59668545518185680422893349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39779030345457120281928899 59668545518185680422893349)
  ·
    refine ⟨11187852284659815079292503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59668545518185680422893349 11187852284659815079292503)
    ·
      refine ⟨16781778426989722618938755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11187852284659815079292503 16781778426989722618938755)
      ·
        refine ⟨25172667640484583928408133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16781778426989722618938755 25172667640484583928408133)
        ·
          refine ⟨4719875182590859486576525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25172667640484583928408133 4719875182590859486576525)
          ·
            refine ⟨1769953193471572307466197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4719875182590859486576525 1769953193471572307466197)
            ·
              refine ⟨41483277971989975956239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1769953193471572307466197 41483277971989975956239)
              ·
                rfl

theorem cell21_1635965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 7].length) (baseStart_1635965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1635965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1635965 prefixEnd_1635965 := by exact prefixLift 1635965
  have htrace : WordTrace (prefixWord ++ tailWord_1635965) baseStart_1635965 baseEnd_1635965 := by
    simpa [prefixWord, tailWord_1635965, baseEnd_1635965] using wordTrace_append hprefix tailTrace_1635965
  have hstable : (prefixWord ++ tailWord_1635965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635965).length < 2 ^ (prefixWord ++ tailWord_1635965).sum := by decide
  have hdescent : baseEnd_1635965 < baseStart_1635965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635993 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 8]
def baseStart_1635993 : Nat := 118140960795 + 1635993 * 2 ^ 59
def prefixEnd_1635993 : Nat := 4983230072969 + 3 ^ 40 * 1635993 * 2
def baseEnd_1635993 : Nat := 373355891729387957139427

theorem tailTrace_1635993 : CollatzResearch.WordTrace tailWord_1635993 prefixEnd_1635993 373355891729387957139427 := by
  unfold tailWord_1635993
  simp only [CollatzResearch.WordTrace]
  refine ⟨59669566762084241204912633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39779711174722827469941755 59669566762084241204912633)
  ·
    refine ⟨44752175071563180903684475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59669566762084241204912633 44752175071563180903684475)
    ·
      refine ⟨67128262607344771355526713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44752175071563180903684475 67128262607344771355526713)
      ·
        refine ⟨50346196955508578516645035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67128262607344771355526713 50346196955508578516645035)
        ·
          refine ⟨75519295433262867774967553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50346196955508578516645035 75519295433262867774967553)
          ·
            refine ⟨56639471574947150831225665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75519295433262867774967553 56639471574947150831225665)
            ·
              refine ⟨42479603681210363123419249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56639471574947150831225665 42479603681210363123419249)
              ·
                refine ⟨31859702760907772342564437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42479603681210363123419249 31859702760907772342564437)
                ·
                  refine ⟨373355891729387957139427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31859702760907772342564437 373355891729387957139427)
                  ·
                    rfl

theorem cell21_1635993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_1635993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1635993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1635993 prefixEnd_1635993 := by exact prefixLift 1635993
  have htrace : WordTrace (prefixWord ++ tailWord_1635993) baseStart_1635993 baseEnd_1635993 := by
    simpa [prefixWord, tailWord_1635993, baseEnd_1635993] using wordTrace_append hprefix tailTrace_1635993
  have hstable : (prefixWord ++ tailWord_1635993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635993).length < 2 ^ (prefixWord ++ tailWord_1635993).sum := by decide
  have hdescent : baseEnd_1635993 < baseStart_1635993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636013 : List Nat := [1, 5, 2, 1, 1, 1, 2, 5, 3]
def baseStart_1636013 : Nat := 118140960795 + 1636013 * 2 ^ 59
def prefixEnd_1636013 : Nat := 4983230072969 + 3 ^ 40 * 1636013 * 2
def baseEnd_1636013 : Nat := 373360456001872366806053

theorem tailTrace_1636013 : CollatzResearch.WordTrace tailWord_1636013 prefixEnd_1636013 373360456001872366806053 := by
  unfold tailWord_1636013
  simp only [CollatzResearch.WordTrace]
  refine ⟨59670296222011784620640693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39780197481341189747093795 59670296222011784620640693)
  ·
    refine ⟨5594090270813604808185065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59670296222011784620640693 5594090270813604808185065)
    ·
      refine ⟨4195567703110203606138799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5594090270813604808185065 4195567703110203606138799)
      ·
        refine ⟨6293351554665305409208199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4195567703110203606138799 6293351554665305409208199)
        ·
          refine ⟨9440027331997958113812299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6293351554665305409208199 9440027331997958113812299)
          ·
            refine ⟨14160040997996937170718449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9440027331997958113812299 14160040997996937170718449)
            ·
              refine ⟨10620030748497702878038837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14160040997996937170718449 10620030748497702878038837)
              ·
                refine ⟨995627882671659644816141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10620030748497702878038837 995627882671659644816141)
                ·
                  refine ⟨373360456001872366806053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 995627882671659644816141 373360456001872366806053)
                  ·
                    rfl

theorem cell21_1636013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_1636013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1636013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1636013 prefixEnd_1636013 := by exact prefixLift 1636013
  have htrace : WordTrace (prefixWord ++ tailWord_1636013) baseStart_1636013 baseEnd_1636013 := by
    simpa [prefixWord, tailWord_1636013, baseEnd_1636013] using wordTrace_append hprefix tailTrace_1636013
  have hstable : (prefixWord ++ tailWord_1636013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636013).length < 2 ^ (prefixWord ++ tailWord_1636013).sum := by decide
  have hdescent : baseEnd_1636013 < baseStart_1636013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636030 : List Nat := [4, 2, 1, 1, 2, 2, 4, 2, 3]
def baseStart_1636030 : Nat := 118140960795 + 1636030 * 2 ^ 59
def prefixEnd_1636030 : Nat := 4983230072969 + 3 ^ 40 * 1636030 * 2
def baseEnd_1636030 : Nat := 373364335633484115022685

theorem tailTrace_1636030 : CollatzResearch.WordTrace tailWord_1636030 prefixEnd_1636030 373364335633484115022685 := by
  unfold tailWord_1636030
  simp only [CollatzResearch.WordTrace]
  refine ⟨7458864532868774565501193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39780610841966797682673029 7458864532868774565501193)
  ·
    refine ⟨5594148399651580924125895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7458864532868774565501193 5594148399651580924125895)
    ·
      refine ⟨8391222599477371386188843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5594148399651580924125895 8391222599477371386188843)
      ·
        refine ⟨12586833899216057079283265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8391222599477371386188843 12586833899216057079283265)
        ·
          refine ⟨9440125424412042809462449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12586833899216057079283265 9440125424412042809462449)
          ·
            refine ⟨7080094068309032107096837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9440125424412042809462449 7080094068309032107096837)
            ·
              refine ⟨1327517637807943520080657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7080094068309032107096837 1327517637807943520080657)
              ·
                refine ⟨995638228355957640060493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1327517637807943520080657 995638228355957640060493)
                ·
                  refine ⟨373364335633484115022685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 995638228355957640060493 373364335633484115022685)
                  ·
                    rfl

theorem cell21_1636030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_1636030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1636030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1636030 prefixEnd_1636030 := by exact prefixLift 1636030
  have htrace : WordTrace (prefixWord ++ tailWord_1636030) baseStart_1636030 baseEnd_1636030 := by
    simpa [prefixWord, tailWord_1636030, baseEnd_1636030] using wordTrace_append hprefix tailTrace_1636030
  have hstable : (prefixWord ++ tailWord_1636030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636030).length < 2 ^ (prefixWord ++ tailWord_1636030).sum := by decide
  have hdescent : baseEnd_1636030 < baseStart_1636030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636055 : List Nat := [1, 1, 3, 2, 1, 3, 3, 2, 5]
def baseStart_1636055 : Nat := 118140960795 + 1636055 * 2 ^ 59
def prefixEnd_1636055 : Nat := 4983230072969 + 3 ^ 40 * 1636055 * 2
def baseEnd_1636055 : Nat := 373370040974089627105967

theorem tailTrace_1636055 : CollatzResearch.WordTrace tailWord_1636055 prefixEnd_1636055 373370040974089627105967 := by
  unfold tailWord_1636055
  simp only [CollatzResearch.WordTrace]
  refine ⟨59671828087859625793669619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39781218725239750529113079 59671828087859625793669619)
  ·
    refine ⟨89507742131789438690504429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59671828087859625793669619 89507742131789438690504429)
    ·
      refine ⟨33565403299421039508939161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89507742131789438690504429 33565403299421039508939161)
      ·
        refine ⟨25174052474565779631704371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33565403299421039508939161 25174052474565779631704371)
        ·
          refine ⟨37761078711848669447556557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25174052474565779631704371 37761078711848669447556557)
          ·
            refine ⟨14160404516943251042833709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37761078711848669447556557 14160404516943251042833709)
            ·
              refine ⟨5310151693853719141062641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14160404516943251042833709 5310151693853719141062641)
              ·
                refine ⟨3982613770390289355796981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5310151693853719141062641 3982613770390289355796981)
                ·
                  refine ⟨373370040974089627105967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3982613770390289355796981 373370040974089627105967)
                  ·
                    rfl

theorem cell21_1636055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 5].length) (baseStart_1636055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1636055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1636055 prefixEnd_1636055 := by exact prefixLift 1636055
  have htrace : WordTrace (prefixWord ++ tailWord_1636055) baseStart_1636055 baseEnd_1636055 := by
    simpa [prefixWord, tailWord_1636055, baseEnd_1636055] using wordTrace_append hprefix tailTrace_1636055
  have hstable : (prefixWord ++ tailWord_1636055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636055).length < 2 ^ (prefixWord ++ tailWord_1636055).sum := by decide
  have hdescent : baseEnd_1636055 < baseStart_1636055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636117 : List Nat := [1, 3, 2, 1, 2, 3, 4, 5]
def baseStart_1636117 : Nat := 118140960795 + 1636117 * 2 ^ 59
def prefixEnd_1636117 : Nat := 4983230072969 + 3 ^ 40 * 1636117 * 2
def baseEnd_1636117 : Nat := 124461396739597099024169

theorem tailTrace_1636117 : CollatzResearch.WordTrace tailWord_1636117 prefixEnd_1636117 124461396739597099024169 := by
  unfold tailWord_1636117
  simp only [CollatzResearch.WordTrace]
  refine ⟨59674089413635010382426605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39782726275756673588284403 59674089413635010382426605)
  ·
    refine ⟨22377783530113128893409977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59674089413635010382426605 22377783530113128893409977)
    ·
      refine ⟨16783337647584846670057483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22377783530113128893409977 16783337647584846670057483)
      ·
        refine ⟨25175006471377270005086225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16783337647584846670057483 25175006471377270005086225)
        ·
          refine ⟨18881254853532952503814669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25175006471377270005086225 18881254853532952503814669)
          ·
            refine ⟨7080470570074857188930501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18881254853532952503814669 7080470570074857188930501)
            ·
              refine ⟨1327588231889035722924469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7080470570074857188930501 1327588231889035722924469)
              ·
                refine ⟨124461396739597099024169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1327588231889035722924469 124461396739597099024169)
                ·
                  rfl

theorem cell21_1636117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 5].length) (baseStart_1636117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1636117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1636117 prefixEnd_1636117 := by exact prefixLift 1636117
  have htrace : WordTrace (prefixWord ++ tailWord_1636117) baseStart_1636117 baseEnd_1636117 := by
    simpa [prefixWord, tailWord_1636117, baseEnd_1636117] using wordTrace_append hprefix tailTrace_1636117
  have hstable : (prefixWord ++ tailWord_1636117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636117).length < 2 ^ (prefixWord ++ tailWord_1636117).sum := by decide
  have hdescent : baseEnd_1636117 < baseStart_1636117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636221 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 8]
def baseStart_1636221 : Nat := 118140960795 + 1636221 * 2 ^ 59
def prefixEnd_1636221 : Nat := 4983230072969 + 3 ^ 40 * 1636221 * 2
def baseEnd_1636221 : Nat := 373407924435710227338961

theorem tailTrace_1636221 : CollatzResearch.WordTrace tailWord_1636221 prefixEnd_1636221 373407924435710227338961 := by
  unfold tailWord_1636221
  simp only [CollatzResearch.WordTrace]
  refine ⟨59677882605258236144212517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39785255070172157429475011 59677882605258236144212517)
  ·
    refine ⟨11189602988485919277039847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59677882605258236144212517 11189602988485919277039847)
    ·
      refine ⟨16784404482728878915559771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11189602988485919277039847 16784404482728878915559771)
      ·
        refine ⟨25176606724093318373339657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16784404482728878915559771 25176606724093318373339657)
        ·
          refine ⟨18882455043069988780004743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25176606724093318373339657 18882455043069988780004743)
          ·
            refine ⟨28323682564604983170007115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18882455043069988780004743 28323682564604983170007115)
            ·
              refine ⟨42485523846907474755010673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28323682564604983170007115 42485523846907474755010673)
              ·
                refine ⟨31864142885180606066258005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42485523846907474755010673 31864142885180606066258005)
                ·
                  refine ⟨373407924435710227338961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31864142885180606066258005 373407924435710227338961)
                  ·
                    rfl

theorem cell21_1636221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_1636221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1636221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1636221 prefixEnd_1636221 := by exact prefixLift 1636221
  have htrace : WordTrace (prefixWord ++ tailWord_1636221) baseStart_1636221 baseEnd_1636221 := by
    simpa [prefixWord, tailWord_1636221, baseEnd_1636221] using wordTrace_append hprefix tailTrace_1636221
  have hstable : (prefixWord ++ tailWord_1636221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636221).length < 2 ^ (prefixWord ++ tailWord_1636221).sum := by decide
  have hdescent : baseEnd_1636221 < baseStart_1636221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636286 : List Nat := [4, 2, 1, 1, 1, 5, 2, 5]
def baseStart_1636286 : Nat := 118140960795 + 1636286 * 2 ^ 59
def prefixEnd_1636286 : Nat := 4983230072969 + 3 ^ 40 * 1636286 * 2
def baseEnd_1636286 : Nat := 124474252773761519585165

theorem tailTrace_1636286 : CollatzResearch.WordTrace tailWord_1636286 prefixEnd_1636286 124474252773761519585165 := by
  unfold tailWord_1636286
  simp only [CollatzResearch.WordTrace]
  refine ⟨7460031668752844030666089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39786835566681834830219141 7460031668752844030666089)
  ·
    refine ⟨5595023751564633022999567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7460031668752844030666089 5595023751564633022999567)
    ·
      refine ⟨8392535627346949534499351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5595023751564633022999567 8392535627346949534499351)
      ·
        refine ⟨12588803441020424301749027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8392535627346949534499351 12588803441020424301749027)
        ·
          refine ⟨18883205161530636452623541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12588803441020424301749027 18883205161530636452623541)
          ·
            refine ⟨1770300483893497167433457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18883205161530636452623541 1770300483893497167433457)
            ·
              refine ⟨1327725362920122875575093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1770300483893497167433457 1327725362920122875575093)
              ·
                refine ⟨124474252773761519585165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1327725362920122875575093 124474252773761519585165)
                ·
                  rfl

theorem cell21_1636286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_1636286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1636286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1636286 prefixEnd_1636286 := by exact prefixLift 1636286
  have htrace : WordTrace (prefixWord ++ tailWord_1636286) baseStart_1636286 baseEnd_1636286 := by
    simpa [prefixWord, tailWord_1636286, baseEnd_1636286] using wordTrace_append hprefix tailTrace_1636286
  have hstable : (prefixWord ++ tailWord_1636286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636286).length < 2 ^ (prefixWord ++ tailWord_1636286).sum := by decide
  have hdescent : baseEnd_1636286 < baseStart_1636286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636317 : List Nat := [1, 4, 3, 1, 3, 2, 1, 1, 5]
def baseStart_1636317 : Nat := 118140960795 + 1636317 * 2 ^ 59
def prefixEnd_1636317 : Nat := 4983230072969 + 3 ^ 40 * 1636317 * 2
def baseEnd_1636317 : Nat := 373429832943635393738765

theorem tailTrace_1636317 : CollatzResearch.WordTrace tailWord_1636317 prefixEnd_1636317 373429832943635393738765 := by
  unfold tailWord_1636317
  simp only [CollatzResearch.WordTrace]
  refine ⟨59681384012910444539707205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39787589341940296359804803 59681384012910444539707205)
  ·
    refine ⟨11190259502420708351195101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59681384012910444539707205 11190259502420708351195101)
    ·
      refine ⟨4196347313407765631698163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11190259502420708351195101 4196347313407765631698163)
      ·
        refine ⟨6294520970111648447547245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4196347313407765631698163 6294520970111648447547245)
        ·
          refine ⟨2360445363791868167830217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6294520970111648447547245 2360445363791868167830217)
          ·
            refine ⟨1770334022843901125872663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2360445363791868167830217 1770334022843901125872663)
            ·
              refine ⟨2655501034265851688808995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1770334022843901125872663 2655501034265851688808995)
              ·
                refine ⟨3983251551398777533213493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2655501034265851688808995 3983251551398777533213493)
                ·
                  refine ⟨373429832943635393738765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3983251551398777533213493 373429832943635393738765)
                  ·
                    rfl

theorem cell21_1636317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_1636317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1636317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1636317 prefixEnd_1636317 := by exact prefixLift 1636317
  have htrace : WordTrace (prefixWord ++ tailWord_1636317) baseStart_1636317 baseEnd_1636317 := by
    simpa [prefixWord, tailWord_1636317, baseEnd_1636317] using wordTrace_append hprefix tailTrace_1636317
  have hstable : (prefixWord ++ tailWord_1636317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636317).length < 2 ^ (prefixWord ++ tailWord_1636317).sum := by decide
  have hdescent : baseEnd_1636317 < baseStart_1636317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636376 : List Nat := [2, 1, 2, 3, 2, 1, 3, 4, 3]
def baseStart_1636376 : Nat := 118140960795 + 1636376 * 2 ^ 59
def prefixEnd_1636376 : Nat := 4983230072969 + 3 ^ 40 * 1636376 * 2
def baseEnd_1636376 : Nat := 373443297547464402255311

theorem tailTrace_1636376 : CollatzResearch.WordTrace tailWord_1636376 prefixEnd_1636376 373443297547464402255311 := by
  unfold tailWord_1636376
  simp only [CollatzResearch.WordTrace]
  refine ⟨29841767959848348808052491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39789023946464465077403321 29841767959848348808052491)
  ·
    refine ⟨44762651939772523212078737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29841767959848348808052491 44762651939772523212078737)
    ·
      refine ⟨33571988954829392409059053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44762651939772523212078737 33571988954829392409059053)
      ·
        refine ⟨12589495858061022153397145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33571988954829392409059053 12589495858061022153397145)
        ·
          refine ⟨9442121893545766615047859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12589495858061022153397145 9442121893545766615047859)
          ·
            refine ⟨14163182840318649922571789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9442121893545766615047859 14163182840318649922571789)
            ·
              refine ⟨5311193565119493720964421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14163182840318649922571789 5311193565119493720964421)
              ·
                refine ⟨995848793459905072680829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5311193565119493720964421 995848793459905072680829)
                ·
                  refine ⟨373443297547464402255311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 995848793459905072680829 373443297547464402255311)
                  ·
                    rfl

theorem cell21_1636376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 3].length) (baseStart_1636376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1636376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1636376 prefixEnd_1636376 := by exact prefixLift 1636376
  have htrace : WordTrace (prefixWord ++ tailWord_1636376) baseStart_1636376 baseEnd_1636376 := by
    simpa [prefixWord, tailWord_1636376, baseEnd_1636376] using wordTrace_append hprefix tailTrace_1636376
  have hstable : (prefixWord ++ tailWord_1636376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636376).length < 2 ^ (prefixWord ++ tailWord_1636376).sum := by decide
  have hdescent : baseEnd_1636376 < baseStart_1636376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636500 : List Nat := [2, 4, 2, 3, 1, 1, 1, 3, 4]
def baseStart_1636500 : Nat := 118140960795 + 1636500 * 2 ^ 59
def prefixEnd_1636500 : Nat := 4983230072969 + 3 ^ 40 * 1636500 * 2
def baseEnd_1636500 : Nat := 373471596036867742188391

theorem tailTrace_1636500 : CollatzResearch.WordTrace tailWord_1636500 prefixEnd_1636500 373471596036867742188391 := by
  unfold tailWord_1636500
  simp only [CollatzResearch.WordTrace]
  refine ⟨29844029285623733396809477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39792039047498311195745969 29844029285623733396809477)
  ·
    refine ⟨5595755491054450011901777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29844029285623733396809477 5595755491054450011901777)
    ·
      refine ⟨4196816618290837508926333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5595755491054450011901777 4196816618290837508926333)
      ·
        refine ⟨1573806231859064065847375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4196816618290837508926333 1573806231859064065847375)
        ·
          refine ⟨2360709347788596098771063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1573806231859064065847375 2360709347788596098771063)
          ·
            refine ⟨3541064021682894148156595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2360709347788596098771063 3541064021682894148156595)
            ·
              refine ⟨5311596032524341222234893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3541064021682894148156595 5311596032524341222234893)
              ·
                refine ⟨1991848512196627958338085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5311596032524341222234893 1991848512196627958338085)
                ·
                  refine ⟨373471596036867742188391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1991848512196627958338085 373471596036867742188391)
                  ·
                    rfl

theorem cell21_1636500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_1636500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1636500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1636500 prefixEnd_1636500 := by exact prefixLift 1636500
  have htrace : WordTrace (prefixWord ++ tailWord_1636500) baseStart_1636500 baseEnd_1636500 := by
    simpa [prefixWord, tailWord_1636500, baseEnd_1636500] using wordTrace_append hprefix tailTrace_1636500
  have hstable : (prefixWord ++ tailWord_1636500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636500).length < 2 ^ (prefixWord ++ tailWord_1636500).sum := by decide
  have hdescent : baseEnd_1636500 < baseStart_1636500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636570 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 7]
def baseStart_1636570 : Nat := 118140960795 + 1636570 * 2 ^ 59
def prefixEnd_1636570 : Nat := 4983230072969 + 3 ^ 40 * 1636570 * 2
def baseEnd_1636570 : Nat := 373487570990563176021581

theorem tailTrace_1636570 : CollatzResearch.WordTrace tailWord_1636570 prefixEnd_1636570 373487570990563176021581 := by
  unfold tailWord_1636570
  simp only [CollatzResearch.WordTrace]
  refine ⟨14922652920248467187166791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39793741120662579165778109 14922652920248467187166791)
  ·
    refine ⟨22383979380372700780750187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14922652920248467187166791 22383979380372700780750187)
    ·
      refine ⟨33575969070559051171125281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22383979380372700780750187 33575969070559051171125281)
      ·
        refine ⟨25181976802919288378343961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33575969070559051171125281 25181976802919288378343961)
        ·
          refine ⟨18886482602189466283757971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25181976802919288378343961 18886482602189466283757971)
          ·
            refine ⟨28329723903284199425636957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18886482602189466283757971 28329723903284199425636957)
            ·
              refine ⟨10623646463731574784613859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28329723903284199425636957 10623646463731574784613859)
              ·
                refine ⟨15935469695597362176920789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10623646463731574784613859 15935469695597362176920789)
                ·
                  refine ⟨373487570990563176021581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15935469695597362176920789 373487570990563176021581)
                  ·
                    rfl

theorem cell21_1636570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_1636570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1636570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1636570 prefixEnd_1636570 := by exact prefixLift 1636570
  have htrace : WordTrace (prefixWord ++ tailWord_1636570) baseStart_1636570 baseEnd_1636570 := by
    simpa [prefixWord, tailWord_1636570, baseEnd_1636570] using wordTrace_append hprefix tailTrace_1636570
  have hstable : (prefixWord ++ tailWord_1636570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636570).length < 2 ^ (prefixWord ++ tailWord_1636570).sum := by decide
  have hdescent : baseEnd_1636570 < baseStart_1636570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636601 : List Nat := [1, 2, 1, 3, 1, 1, 2, 6, 4]
def baseStart_1636601 : Nat := 118140960795 + 1636601 * 2 ^ 59
def prefixEnd_1636601 : Nat := 4983230072969 + 3 ^ 40 * 1636601 * 2
def baseEnd_1636601 : Nat := 373494645612914011004851

theorem tailTrace_1636601 : CollatzResearch.WordTrace tailWord_1636601 prefixEnd_1636601 373494645612914011004851 := by
  unfold tailWord_1636601
  simp only [CollatzResearch.WordTrace]
  refine ⟨59691742343881561043045657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39794494895921040695363771 59691742343881561043045657)
  ·
    refine ⟨44768806757911170782284243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59691742343881561043045657 44768806757911170782284243)
    ·
      refine ⟨67153210136866756173426365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44768806757911170782284243 67153210136866756173426365)
      ·
        refine ⟨25182453801325033565034887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67153210136866756173426365 25182453801325033565034887)
        ·
          refine ⟨37773680701987550347552331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25182453801325033565034887 37773680701987550347552331)
          ·
            refine ⟨56660521052981325521328497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37773680701987550347552331 56660521052981325521328497)
            ·
              refine ⟨42495390789735994140996373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56660521052981325521328497 42495390789735994140996373)
              ·
                refine ⟨1991971443268874725359205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42495390789735994140996373 1991971443268874725359205)
                ·
                  refine ⟨373494645612914011004851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1991971443268874725359205 373494645612914011004851)
                  ·
                    rfl

theorem cell21_1636601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 4].length) (baseStart_1636601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1636601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1636601 prefixEnd_1636601 := by exact prefixLift 1636601
  have htrace : WordTrace (prefixWord ++ tailWord_1636601) baseStart_1636601 baseEnd_1636601 := by
    simpa [prefixWord, tailWord_1636601, baseEnd_1636601] using wordTrace_append hprefix tailTrace_1636601
  have hstable : (prefixWord ++ tailWord_1636601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636601).length < 2 ^ (prefixWord ++ tailWord_1636601).sum := by decide
  have hdescent : baseEnd_1636601 < baseStart_1636601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636604 : List Nat := [2, 2, 2, 1, 4, 1, 2, 4, 3]
def baseStart_1636604 : Nat := 118140960795 + 1636604 * 2 ^ 59
def prefixEnd_1636604 : Nat := 4983230072969 + 3 ^ 40 * 1636604 * 2
def baseEnd_1636604 : Nat := 373495330253786672454845

theorem tailTrace_1636604 : CollatzResearch.WordTrace tailWord_1636604 prefixEnd_1636604 373495330253786672454845 := by
  unfold tailWord_1636604
  simp only [CollatzResearch.WordTrace]
  refine ⟨29845925881435346277702433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39794567841913795036936577 29845925881435346277702433)
  ·
    refine ⟨22384444411076509708276825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29845925881435346277702433 22384444411076509708276825)
    ·
      refine ⟨16788333308307382281207619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22384444411076509708276825 16788333308307382281207619)
      ·
        refine ⟨25182499962461073421811429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16788333308307382281207619 25182499962461073421811429)
        ·
          refine ⟨4721718742961451266589643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25182499962461073421811429 4721718742961451266589643)
          ·
            refine ⟨7082578114442176899884465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4721718742961451266589643 7082578114442176899884465)
            ·
              refine ⟨5311933585831632674913349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7082578114442176899884465 5311933585831632674913349)
              ·
                refine ⟨995987547343431126546253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5311933585831632674913349 995987547343431126546253)
                ·
                  refine ⟨373495330253786672454845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 995987547343431126546253 373495330253786672454845)
                  ·
                    rfl

theorem cell21_1636604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4, 3].length) (baseStart_1636604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1636604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1636604 prefixEnd_1636604 := by exact prefixLift 1636604
  have htrace : WordTrace (prefixWord ++ tailWord_1636604) baseStart_1636604 baseEnd_1636604 := by
    simpa [prefixWord, tailWord_1636604, baseEnd_1636604] using wordTrace_append hprefix tailTrace_1636604
  have hstable : (prefixWord ++ tailWord_1636604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636604).length < 2 ^ (prefixWord ++ tailWord_1636604).sum := by decide
  have hdescent : baseEnd_1636604 < baseStart_1636604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636638 : List Nat := [4, 3, 2, 1, 1, 1, 3, 3, 3]
def baseStart_1636638 : Nat := 118140960795 + 1636638 * 2 ^ 59
def prefixEnd_1636638 : Nat := 4983230072969 + 3 ^ 40 * 1636638 * 2
def baseEnd_1636638 : Nat := 373503089517010168888109

theorem tailTrace_1636638 : CollatzResearch.WordTrace tailWord_1636638 prefixEnd_1636638 373503089517010168888109 := by
  unfold tailWord_1636638
  simp only [CollatzResearch.WordTrace]
  refine ⟨7461636480593439545267821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39795394563165010908095045 7461636480593439545267821)
  ·
    refine ⟨2798113680222539829475433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7461636480593439545267821 2798113680222539829475433)
    ·
      refine ⟨2098585260166904872106575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2798113680222539829475433 2098585260166904872106575)
      ·
        refine ⟨3147877890250357308159863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2098585260166904872106575 3147877890250357308159863)
        ·
          refine ⟨4721816835375535962239795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3147877890250357308159863 4721816835375535962239795)
          ·
            refine ⟨7082725253063303943359693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4721816835375535962239795 7082725253063303943359693)
            ·
              refine ⟨2656021969898738978759885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7082725253063303943359693 2656021969898738978759885)
              ·
                refine ⟨996008238712027117034957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2656021969898738978759885 996008238712027117034957)
                ·
                  refine ⟨373503089517010168888109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 996008238712027117034957 373503089517010168888109)
                  ·
                    rfl

theorem cell21_1636638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_1636638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1636638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1636638 prefixEnd_1636638 := by exact prefixLift 1636638
  have htrace : WordTrace (prefixWord ++ tailWord_1636638) baseStart_1636638 baseEnd_1636638 := by
    simpa [prefixWord, tailWord_1636638, baseEnd_1636638] using wordTrace_append hprefix tailTrace_1636638
  have hstable : (prefixWord ++ tailWord_1636638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636638).length < 2 ^ (prefixWord ++ tailWord_1636638).sum := by decide
  have hdescent : baseEnd_1636638 < baseStart_1636638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636663 : List Nat := [1, 1, 3, 1, 2, 1, 1, 8, 3]
def baseStart_1636663 : Nat := 118140960795 + 1636663 * 2 ^ 59
def prefixEnd_1636663 : Nat := 4983230072969 + 3 ^ 40 * 1636663 * 2
def baseEnd_1636663 : Nat := 373508794857615680971391

theorem tailTrace_1636663 : CollatzResearch.WordTrace tailWord_1636663 prefixEnd_1636663 373508794857615680971391 := by
  unfold tailWord_1636663
  simp only [CollatzResearch.WordTrace]
  refine ⟨59694003669656945631802643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39796002446437963754535095 59694003669656945631802643)
  ·
    refine ⟨89541005504485418447703965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59694003669656945631802643 89541005504485418447703965)
    ·
      refine ⟨33577877064182031917888987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89541005504485418447703965 33577877064182031917888987)
      ·
        refine ⟨50366815596273047876833481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33577877064182031917888987 50366815596273047876833481)
        ·
          refine ⟨37775111697204785907625111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50366815596273047876833481 37775111697204785907625111)
          ·
            refine ⟨56662667545807178861437667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37775111697204785907625111 56662667545807178861437667)
            ·
              refine ⟨84994001318710768292156501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56662667545807178861437667 84994001318710768292156501)
              ·
                refine ⟨996023452953641815923709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 84994001318710768292156501 996023452953641815923709)
                ·
                  refine ⟨373508794857615680971391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 996023452953641815923709 373508794857615680971391)
                  ·
                    rfl

theorem cell21_1636663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8, 3].length) (baseStart_1636663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1636663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1636663 prefixEnd_1636663 := by exact prefixLift 1636663
  have htrace : WordTrace (prefixWord ++ tailWord_1636663) baseStart_1636663 baseEnd_1636663 := by
    simpa [prefixWord, tailWord_1636663, baseEnd_1636663] using wordTrace_append hprefix tailTrace_1636663
  have hstable : (prefixWord ++ tailWord_1636663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636663).length < 2 ^ (prefixWord ++ tailWord_1636663).sum := by decide
  have hdescent : baseEnd_1636663 < baseStart_1636663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636714 : List Nat := [3, 1, 3, 3, 1, 3, 2, 2, 3]
def baseStart_1636714 : Nat := 118140960795 + 1636714 * 2 ^ 59
def prefixEnd_1636714 : Nat := 4983230072969 + 3 ^ 40 * 1636714 * 2
def baseEnd_1636714 : Nat := 373520433752450925621287

theorem tailTrace_1636714 : CollatzResearch.WordTrace tailWord_1636714 prefixEnd_1636714 373520433752450925621287 := by
  unfold tailWord_1636714
  simp only [CollatzResearch.WordTrace]
  refine ⟨14923965948118045335477299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39797242528314787561272797 14923965948118045335477299)
  ·
    refine ⟨22385948922177068003215949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14923965948118045335477299 22385948922177068003215949)
    ·
      refine ⟨8394730845816400501205981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22385948922177068003215949 8394730845816400501205981)
      ·
        refine ⟨3148024067181150187952243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8394730845816400501205981 3148024067181150187952243)
        ·
          refine ⟨4722036100771725281928365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3148024067181150187952243 4722036100771725281928365)
          ·
            refine ⟨1770763537789396980723137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4722036100771725281928365 1770763537789396980723137)
            ·
              refine ⟨1328072653342047735542353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1770763537789396980723137 1328072653342047735542353)
              ·
                refine ⟨996054490006535801656765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1328072653342047735542353 996054490006535801656765)
                ·
                  refine ⟨373520433752450925621287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 996054490006535801656765 373520433752450925621287)
                  ·
                    rfl

theorem cell21_1636714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2, 3].length) (baseStart_1636714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1636714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1636714 prefixEnd_1636714 := by exact prefixLift 1636714
  have htrace : WordTrace (prefixWord ++ tailWord_1636714) baseStart_1636714 baseEnd_1636714 := by
    simpa [prefixWord, tailWord_1636714, baseEnd_1636714] using wordTrace_append hprefix tailTrace_1636714
  have hstable : (prefixWord ++ tailWord_1636714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636714).length < 2 ^ (prefixWord ++ tailWord_1636714).sum := by decide
  have hdescent : baseEnd_1636714 < baseStart_1636714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636725 : List Nat := [1, 3, 4, 1, 2, 3, 1, 6]
def baseStart_1636725 : Nat := 118140960795 + 1636725 * 2 ^ 59
def prefixEnd_1636725 : Nat := 4983230072969 + 3 ^ 40 * 1636725 * 2
def baseEnd_1636725 : Nat := 124507648034105783645977

theorem tailTrace_1636725 : CollatzResearch.WordTrace tailWord_1636725 prefixEnd_1636725 124507648034105783645977 := by
  unfold tailWord_1636725
  simp only [CollatzResearch.WordTrace]
  refine ⟨59696264995432330220559629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39797509996954886813706419 59696264995432330220559629)
  ·
    refine ⟨22386099373287123832709861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59696264995432330220559629 22386099373287123832709861)
    ·
      refine ⟨4197393632491335718633099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22386099373287123832709861 4197393632491335718633099)
      ·
        refine ⟨6296090448737003577949649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4197393632491335718633099 6296090448737003577949649)
        ·
          refine ⟨4722067836552752683462237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6296090448737003577949649 4722067836552752683462237)
          ·
            refine ⟨1770775438707282256298339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4722067836552752683462237 1770775438707282256298339)
            ·
              refine ⟨2656163158060923384447509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1770775438707282256298339 2656163158060923384447509)
              ·
                refine ⟨124507648034105783645977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2656163158060923384447509 124507648034105783645977)
                ·
                  rfl

theorem cell21_1636725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 6].length) (baseStart_1636725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1636725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1636725 prefixEnd_1636725 := by exact prefixLift 1636725
  have htrace : WordTrace (prefixWord ++ tailWord_1636725) baseStart_1636725 baseEnd_1636725 := by
    simpa [prefixWord, tailWord_1636725, baseEnd_1636725] using wordTrace_append hprefix tailTrace_1636725
  have hstable : (prefixWord ++ tailWord_1636725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636725).length < 2 ^ (prefixWord ++ tailWord_1636725).sum := by decide
  have hdescent : baseEnd_1636725 < baseStart_1636725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636736 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 10]
def baseStart_1636736 : Nat := 118140960795 + 1636736 * 2 ^ 59
def prefixEnd_1636736 : Nat := 4983230072969 + 3 ^ 40 * 1636736 * 2
def baseEnd_1636736 : Nat := 373525454452183776254575

theorem tailTrace_1636736 : CollatzResearch.WordTrace tailWord_1636736 prefixEnd_1636736 373525454452183776254575 := by
  unfold tailWord_1636736
  simp only [CollatzResearch.WordTrace]
  refine ⟨29848333099196239549605031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39797777465594986066140041 29848333099196239549605031)
  ·
    refine ⟨44772499648794359324407547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29848333099196239549605031 44772499648794359324407547)
    ·
      refine ⟨67158749473191538986611321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44772499648794359324407547 67158749473191538986611321)
      ·
        refine ⟨50369062104893654239958491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67158749473191538986611321 50369062104893654239958491)
        ·
          refine ⟨75553593157340481359937737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50369062104893654239958491 75553593157340481359937737)
          ·
            refine ⟨56665194868005361019953303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75553593157340481359937737 56665194868005361019953303)
            ·
              refine ⟨84997792302008041529929955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56665194868005361019953303 84997792302008041529929955)
              ·
                refine ⟨127496688453012062294894933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84997792302008041529929955 127496688453012062294894933)
                ·
                  refine ⟨373525454452183776254575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 127496688453012062294894933 373525454452183776254575)
                  ·
                    rfl

theorem cell21_1636736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_1636736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1636736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1636736 prefixEnd_1636736 := by exact prefixLift 1636736
  have htrace : WordTrace (prefixWord ++ tailWord_1636736) baseStart_1636736 baseEnd_1636736 := by
    simpa [prefixWord, tailWord_1636736, baseEnd_1636736] using wordTrace_append hprefix tailTrace_1636736
  have hstable : (prefixWord ++ tailWord_1636736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636736).length < 2 ^ (prefixWord ++ tailWord_1636736).sum := by decide
  have hdescent : baseEnd_1636736 < baseStart_1636736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636739 : List Nat := [1, 1, 1, 3, 6, 1, 1, 2, 5]
def baseStart_1636739 : Nat := 118140960795 + 1636739 * 2 ^ 59
def prefixEnd_1636739 : Nat := 4983230072969 + 3 ^ 40 * 1636739 * 2
def baseEnd_1636739 : Nat := 373526139093056437704569

theorem tailTrace_1636739 : CollatzResearch.WordTrace tailWord_1636739 prefixEnd_1636739 373526139093056437704569 := by
  unfold tailWord_1636739
  simp only [CollatzResearch.WordTrace]
  refine ⟨59696775617381610611569271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39797850411587740407712847 59696775617381610611569271)
  ·
    refine ⟨89545163426072415917353907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59696775617381610611569271 89545163426072415917353907)
    ·
      refine ⟨134317745139108623876030861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89545163426072415917353907 134317745139108623876030861)
      ·
        refine ⟨50369154427165733953511573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134317745139108623876030861 50369154427165733953511573)
        ·
          refine ⟨2361054113773393779070855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50369154427165733953511573 2361054113773393779070855)
          ·
            refine ⟨3541581170660090668606283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2361054113773393779070855 3541581170660090668606283)
            ·
              refine ⟨5312371755990136002909425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3541581170660090668606283 5312371755990136002909425)
              ·
                refine ⟨3984278816992602002182069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5312371755990136002909425 3984278816992602002182069)
                ·
                  refine ⟨373526139093056437704569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3984278816992602002182069 373526139093056437704569)
                  ·
                    rfl

theorem cell21_1636739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 5].length) (baseStart_1636739 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1636739 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1636739 prefixEnd_1636739 := by exact prefixLift 1636739
  have htrace : WordTrace (prefixWord ++ tailWord_1636739) baseStart_1636739 baseEnd_1636739 := by
    simpa [prefixWord, tailWord_1636739, baseEnd_1636739] using wordTrace_append hprefix tailTrace_1636739
  have hstable : (prefixWord ++ tailWord_1636739).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636739).length < 2 ^ (prefixWord ++ tailWord_1636739).sum := by decide
  have hdescent : baseEnd_1636739 < baseStart_1636739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636767 : List Nat := [1, 1, 2, 5, 1, 1, 10]
def baseStart_1636767 : Nat := 118140960795 + 1636767 * 2 ^ 59
def prefixEnd_1636767 : Nat := 4983230072969 + 3 ^ 40 * 1636767 * 2
def baseEnd_1636767 : Nat := 41503614341614956804205

theorem tailTrace_1636767 : CollatzResearch.WordTrace tailWord_1636767 prefixEnd_1636767 41503614341614956804205 := by
  unfold tailWord_1636767
  simp only [CollatzResearch.WordTrace]
  refine ⟨59697796861280171393588555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39798531240853447595725703 59697796861280171393588555)
  ·
    refine ⟨89546695291920257090382833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59697796861280171393588555 89546695291920257090382833)
    ·
      refine ⟨67160021468940192817787125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89546695291920257090382833 67160021468940192817787125)
      ·
        refine ⟨6296252012713143076667543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67160021468940192817787125 6296252012713143076667543)
        ·
          refine ⟨9444378019069714615001315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6296252012713143076667543 9444378019069714615001315)
          ·
            refine ⟨14166567028604571922501973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9444378019069714615001315 14166567028604571922501973)
            ·
              refine ⟨41503614341614956804205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14166567028604571922501973 41503614341614956804205)
              ·
                rfl

theorem cell21_1636767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 10].length) (baseStart_1636767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1636767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1636767 prefixEnd_1636767 := by exact prefixLift 1636767
  have htrace : WordTrace (prefixWord ++ tailWord_1636767) baseStart_1636767 baseEnd_1636767 := by
    simpa [prefixWord, tailWord_1636767, baseEnd_1636767] using wordTrace_append hprefix tailTrace_1636767
  have hstable : (prefixWord ++ tailWord_1636767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636767).length < 2 ^ (prefixWord ++ tailWord_1636767).sum := by decide
  have hdescent : baseEnd_1636767 < baseStart_1636767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636818 : List Nat := [3, 2, 2, 4, 2, 1, 7]
def baseStart_1636818 : Nat := 118140960795 + 1636818 * 2 ^ 59
def prefixEnd_1636818 : Nat := 4983230072969 + 3 ^ 40 * 1636818 * 2
def baseEnd_1636818 : Nat := 41504907552152206209749

theorem tailTrace_1636818 : CollatzResearch.WordTrace tailWord_1636818 prefixEnd_1636818 41504907552152206209749 := by
  unfold tailWord_1636818
  simp only [CollatzResearch.WordTrace]
  refine ⟨14924914246023851775923777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39799771322730271402463405 14924914246023851775923777)
  ·
    refine ⟨11193685684517888831942833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14924914246023851775923777 11193685684517888831942833)
    ·
      refine ⟨8395264263388416623957125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11193685684517888831942833 8395264263388416623957125)
      ·
        refine ⟨1574112049385328116991961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8395264263388416623957125 1574112049385328116991961)
        ·
          refine ⟨1180584037038996087743971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1574112049385328116991961 1180584037038996087743971)
          ·
            refine ⟨1770876055558494131615957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1180584037038996087743971 1770876055558494131615957)
            ·
              refine ⟨41504907552152206209749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1770876055558494131615957 41504907552152206209749)
              ·
                rfl

theorem cell21_1636818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 7].length) (baseStart_1636818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1636818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1636818 prefixEnd_1636818 := by exact prefixLift 1636818
  have htrace : WordTrace (prefixWord ++ tailWord_1636818) baseStart_1636818 baseEnd_1636818 := by
    simpa [prefixWord, tailWord_1636818, baseEnd_1636818] using wordTrace_append hprefix tailTrace_1636818
  have hstable : (prefixWord ++ tailWord_1636818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636818).length < 2 ^ (prefixWord ++ tailWord_1636818).sum := by decide
  have hdescent : baseEnd_1636818 < baseStart_1636818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636829 : List Nat := [1, 4, 3, 1, 1, 1, 1, 3, 6]
def baseStart_1636829 : Nat := 118140960795 + 1636829 * 2 ^ 59
def prefixEnd_1636829 : Nat := 4983230072969 + 3 ^ 40 * 1636829 * 2
def baseEnd_1636829 : Nat := 373546678319236281204385

theorem tailTrace_1636829 : CollatzResearch.WordTrace tailWord_1636829 prefixEnd_1636829 373546678319236281204385 := by
  unfold tailWord_1636829
  simp only [CollatzResearch.WordTrace]
  refine ⟨59700058187055555982345541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39800038791370370654897027 59700058187055555982345541)
  ·
    refine ⟨11193760910072916746689789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59700058187055555982345541 11193760910072916746689789)
    ·
      refine ⟨4197660341277343780008671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11193760910072916746689789 4197660341277343780008671)
      ·
        refine ⟨6296490511916015670013007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4197660341277343780008671 6296490511916015670013007)
        ·
          refine ⟨9444735767874023505019511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6296490511916015670013007 9444735767874023505019511)
          ·
            refine ⟨14167103651811035257529267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9444735767874023505019511 14167103651811035257529267)
            ·
              refine ⟨21250655477716552886293901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14167103651811035257529267 21250655477716552886293901)
              ·
                refine ⟨7968995804143707332360213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21250655477716552886293901 7968995804143707332360213)
                ·
                  refine ⟨373546678319236281204385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7968995804143707332360213 373546678319236281204385)
                  ·
                    rfl

theorem cell21_1636829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_1636829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1636829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1636829 prefixEnd_1636829 := by exact prefixLift 1636829
  have htrace : WordTrace (prefixWord ++ tailWord_1636829) baseStart_1636829 baseEnd_1636829 := by
    simpa [prefixWord, tailWord_1636829, baseEnd_1636829] using wordTrace_append hprefix tailTrace_1636829
  have hstable : (prefixWord ++ tailWord_1636829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636829).length < 2 ^ (prefixWord ++ tailWord_1636829).sum := by decide
  have hdescent : baseEnd_1636829 < baseStart_1636829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636832 : List Nat := [2, 1, 1, 3, 1, 1, 7, 2, 3]
def baseStart_1636832 : Nat := 118140960795 + 1636832 * 2 ^ 59
def prefixEnd_1636832 : Nat := 4983230072969 + 3 ^ 40 * 1636832 * 2
def baseEnd_1636832 : Nat := 373547362960108942654379

theorem tailTrace_1636832 : CollatzResearch.WordTrace tailWord_1636832 prefixEnd_1636832 373547362960108942654379 := by
  unfold tailWord_1636832
  simp only [CollatzResearch.WordTrace]
  refine ⟨29850083803022343747352375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39800111737363124996469833 29850083803022343747352375)
  ·
    refine ⟨44775125704533515621028563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29850083803022343747352375 44775125704533515621028563)
    ·
      refine ⟨67162688556800273431542845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44775125704533515621028563 67162688556800273431542845)
      ·
        refine ⟨25186008208800102536828567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67162688556800273431542845 25186008208800102536828567)
        ·
          refine ⟨37779012313200153805242851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25186008208800102536828567 37779012313200153805242851)
          ·
            refine ⟨56668518469800230707864277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37779012313200153805242851 56668518469800230707864277)
            ·
              refine ⟨1328168401635942907215569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 56668518469800230707864277 1328168401635942907215569)
              ·
                refine ⟨996126301226957180411677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1328168401635942907215569 996126301226957180411677)
                ·
                  refine ⟨373547362960108942654379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 996126301226957180411677 373547362960108942654379)
                  ·
                    rfl

theorem cell21_1636832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2, 3].length) (baseStart_1636832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1636832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1636832 prefixEnd_1636832 := by exact prefixLift 1636832
  have htrace : WordTrace (prefixWord ++ tailWord_1636832) baseStart_1636832 baseEnd_1636832 := by
    simpa [prefixWord, tailWord_1636832, baseEnd_1636832] using wordTrace_append hprefix tailTrace_1636832
  have hstable : (prefixWord ++ tailWord_1636832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636832).length < 2 ^ (prefixWord ++ tailWord_1636832).sum := by decide
  have hdescent : baseEnd_1636832 < baseStart_1636832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636843 : List Nat := [1, 1, 1, 1, 2, 3, 6, 6]
def baseStart_1636843 : Nat := 118140960795 + 1636843 * 2 ^ 59
def prefixEnd_1636843 : Nat := 4983230072969 + 3 ^ 40 * 1636843 * 2
def baseEnd_1636843 : Nat := 124516624436658455990341

theorem tailTrace_1636843 : CollatzResearch.WordTrace tailWord_1636843 prefixEnd_1636843 124516624436658455990341 := by
  unfold tailWord_1636843
  simp only [CollatzResearch.WordTrace]
  refine ⟨59700568809004836373355183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39800379206003224248903455 59700568809004836373355183)
  ·
    refine ⟨89550853213507254560032775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59700568809004836373355183 89550853213507254560032775)
    ·
      refine ⟨134326279820260881840049163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89550853213507254560032775 134326279820260881840049163)
      ·
        refine ⟨201489419730391322760073745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134326279820260881840049163 201489419730391322760073745)
        ·
          refine ⟨151117064797793492070055309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201489419730391322760073745 151117064797793492070055309)
          ·
            refine ⟨56668899299172559526270741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151117064797793492070055309 56668899299172559526270741)
            ·
              refine ⟨2656354654648713727793941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56668899299172559526270741 2656354654648713727793941)
              ·
                refine ⟨124516624436658455990341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2656354654648713727793941 124516624436658455990341)
                ·
                  rfl

theorem cell21_1636843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 6].length) (baseStart_1636843 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1636843 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1636843 prefixEnd_1636843 := by exact prefixLift 1636843
  have htrace : WordTrace (prefixWord ++ tailWord_1636843) baseStart_1636843 baseEnd_1636843 := by
    simpa [prefixWord, tailWord_1636843, baseEnd_1636843] using wordTrace_append hprefix tailTrace_1636843
  have hstable : (prefixWord ++ tailWord_1636843).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636843).length < 2 ^ (prefixWord ++ tailWord_1636843).sum := by decide
  have hdescent : baseEnd_1636843 < baseStart_1636843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636846 : List Nat := [4, 1, 2, 1, 2, 3, 1, 3, 4]
def baseStart_1636846 : Nat := 118140960795 + 1636846 * 2 ^ 59
def prefixEnd_1636846 : Nat := 4983230072969 + 3 ^ 40 * 1636846 * 2
def baseEnd_1636846 : Nat := 373550557950848029421017

theorem tailTrace_1636846 : CollatzResearch.WordTrace tailWord_1636846 prefixEnd_1636846 373550557950848029421017 := by
  unfold tailWord_1636846
  simp only [CollatzResearch.WordTrace]
  refine ⟨7462584778499245985714299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39800452151995978590476261 7462584778499245985714299)
  ·
    refine ⟨11193877167748868978571449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7462584778499245985714299 11193877167748868978571449)
    ·
      refine ⟨8395407875811651733928587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11193877167748868978571449 8395407875811651733928587)
      ·
        refine ⟨12593111813717477600892881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8395407875811651733928587 12593111813717477600892881)
        ·
          refine ⟨9444833860288108200669661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12593111813717477600892881 9444833860288108200669661)
          ·
            refine ⟨3541812697608040575251123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9444833860288108200669661 3541812697608040575251123)
            ·
              refine ⟨5312719046412060862876685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3541812697608040575251123 5312719046412060862876685)
              ·
                refine ⟨1992269642404522823578757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5312719046412060862876685 1992269642404522823578757)
                ·
                  refine ⟨373550557950848029421017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1992269642404522823578757 373550557950848029421017)
                  ·
                    rfl

theorem cell21_1636846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_1636846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1636846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1636846 prefixEnd_1636846 := by exact prefixLift 1636846
  have htrace : WordTrace (prefixWord ++ tailWord_1636846) baseStart_1636846 baseEnd_1636846 := by
    simpa [prefixWord, tailWord_1636846, baseEnd_1636846] using wordTrace_append hprefix tailTrace_1636846
  have hstable : (prefixWord ++ tailWord_1636846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636846).length < 2 ^ (prefixWord ++ tailWord_1636846).sum := by decide
  have hdescent : baseEnd_1636846 < baseStart_1636846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636877 : List Nat := [1, 7, 1, 1, 1, 10]
def baseStart_1636877 : Nat := 118140960795 + 1636877 * 2 ^ 59
def prefixEnd_1636877 : Nat := 4983230072969 + 3 ^ 40 * 1636877 * 2
def baseEnd_1636877 : Nat := 13835467873081439422381

theorem tailTrace_1636877 : CollatzResearch.WordTrace tailWord_1636877 prefixEnd_1636877 13835467873081439422381 := by
  unfold tailWord_1636877
  simp only [CollatzResearch.WordTrace]
  refine ⟨59701808890881660180092885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39801205927254440120061923 59701808890881660180092885)
  ·
    refine ⟨1399261145880038910470927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 59701808890881660180092885 1399261145880038910470927)
    ·
      refine ⟨2098891718820058365706391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1399261145880038910470927 2098891718820058365706391)
      ·
        refine ⟨3148337578230087548559587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2098891718820058365706391 3148337578230087548559587)
        ·
          refine ⟨4722506367345131322839381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3148337578230087548559587 4722506367345131322839381)
          ·
            refine ⟨13835467873081439422381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4722506367345131322839381 13835467873081439422381)
            ·
              rfl

theorem cell21_1636877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 10].length) (baseStart_1636877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1636877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1636877 prefixEnd_1636877 := by exact prefixLift 1636877
  have htrace : WordTrace (prefixWord ++ tailWord_1636877) baseStart_1636877 baseEnd_1636877 := by
    simpa [prefixWord, tailWord_1636877, baseEnd_1636877] using wordTrace_append hprefix tailTrace_1636877
  have hstable : (prefixWord ++ tailWord_1636877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636877).length < 2 ^ (prefixWord ++ tailWord_1636877).sum := by decide
  have hdescent : baseEnd_1636877 < baseStart_1636877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637012 : List Nat := [2, 4, 2, 2, 1, 1, 1, 8]
def baseStart_1637012 : Nat := 118140960795 + 1637012 * 2 ^ 59
def prefixEnd_1637012 : Nat := 4983230072969 + 3 ^ 40 * 1637012 * 2
def baseEnd_1637012 : Nat := 124529480470822876551337

theorem tailTrace_1637012 : CollatzResearch.WordTrace tailWord_1637012 prefixEnd_1637012 124529480470822876551337 := by
  unfold tailWord_1637012
  simp only [CollatzResearch.WordTrace]
  refine ⟨29853366372696289118128645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39804488496928385490838193 29853366372696289118128645)
  ·
    refine ⟨5597506194880554209649121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29853366372696289118128645 5597506194880554209649121)
    ·
      refine ⟨4198129646160415657236841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5597506194880554209649121 4198129646160415657236841)
      ·
        refine ⟨3148597234620311742927631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4198129646160415657236841 3148597234620311742927631)
        ·
          refine ⟨4722895851930467614391447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3148597234620311742927631 4722895851930467614391447)
          ·
            refine ⟨7084343777895701421587171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4722895851930467614391447 7084343777895701421587171)
            ·
              refine ⟨10626515666843552132380757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7084343777895701421587171 10626515666843552132380757)
              ·
                refine ⟨124529480470822876551337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10626515666843552132380757 124529480470822876551337)
                ·
                  rfl

theorem cell21_1637012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 8].length) (baseStart_1637012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1637012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1637012 prefixEnd_1637012 := by exact prefixLift 1637012
  have htrace : WordTrace (prefixWord ++ tailWord_1637012) baseStart_1637012 baseEnd_1637012 := by
    simpa [prefixWord, tailWord_1637012, baseEnd_1637012] using wordTrace_append hprefix tailTrace_1637012
  have hstable : (prefixWord ++ tailWord_1637012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637012).length < 2 ^ (prefixWord ++ tailWord_1637012).sum := by decide
  have hdescent : baseEnd_1637012 < baseStart_1637012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637060 : List Nat := [2, 3, 3, 1, 1, 3, 1, 4, 3]
def baseStart_1637060 : Nat := 118140960795 + 1637060 * 2 ^ 59
def prefixEnd_1637060 : Nat := 4983230072969 + 3 ^ 40 * 1637060 * 2
def baseEnd_1637060 : Nat := 373599395666431212853913

theorem tailTrace_1637060 : CollatzResearch.WordTrace tailWord_1637060 prefixEnd_1637060 373599395666431212853913 := by
  unfold tailWord_1637060
  simp only [CollatzResearch.WordTrace]
  refine ⟨29854241724609341217002317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39805655632812454956003089 29854241724609341217002317)
  ·
    refine ⟨11195340646728502956375869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29854241724609341217002317 11195340646728502956375869)
    ·
      refine ⟨4198252742523188608640951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11195340646728502956375869 4198252742523188608640951)
      ·
        refine ⟨6297379113784782912961427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4198252742523188608640951 6297379113784782912961427)
        ·
          refine ⟨9446068670677174369442141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6297379113784782912961427 9446068670677174369442141)
          ·
            refine ⟨3542275751503940388540803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9446068670677174369442141 3542275751503940388540803)
            ·
              refine ⟨5313413627255910582811205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3542275751503940388540803 5313413627255910582811205)
              ·
                refine ⟨996265055110483234277101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5313413627255910582811205 996265055110483234277101)
                ·
                  refine ⟨373599395666431212853913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 996265055110483234277101 373599395666431212853913)
                  ·
                    rfl

theorem cell21_1637060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_1637060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1637060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1637060 prefixEnd_1637060 := by exact prefixLift 1637060
  have htrace : WordTrace (prefixWord ++ tailWord_1637060) baseStart_1637060 baseEnd_1637060 := by
    simpa [prefixWord, tailWord_1637060, baseEnd_1637060] using wordTrace_append hprefix tailTrace_1637060
  have hstable : (prefixWord ++ tailWord_1637060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637060).length < 2 ^ (prefixWord ++ tailWord_1637060).sum := by decide
  have hdescent : baseEnd_1637060 < baseStart_1637060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637271 : List Nat := [1, 1, 3, 3, 1, 2, 4, 3, 3]
def baseStart_1637271 : Nat := 118140960795 + 1637271 * 2 ^ 59
def prefixEnd_1637271 : Nat := 4983230072969 + 3 ^ 40 * 1637271 * 2
def baseEnd_1637271 : Nat := 373647548741141734836815

theorem tailTrace_1637271 : CollatzResearch.WordTrace tailWord_1637271 prefixEnd_1637271 373647548741141734836815 := by
  unfold tailWord_1637271
  simp only [CollatzResearch.WordTrace]
  refine ⟨59716179251454265469935667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39810786167636176979957111 59716179251454265469935667)
  ·
    refine ⟨89574268877181398204903501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59716179251454265469935667 89574268877181398204903501)
    ·
      refine ⟨33590350828943024326838813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89574268877181398204903501 33590350828943024326838813)
      ·
        refine ⟨12596381560853634122564555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33590350828943024326838813 12596381560853634122564555)
        ·
          refine ⟨18894572341280451183846833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12596381560853634122564555 18894572341280451183846833)
          ·
            refine ⟨14170929255960338387885125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18894572341280451183846833 14170929255960338387885125)
            ·
              refine ⟨2657049235492563447728461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14170929255960338387885125 2657049235492563447728461)
              ·
                refine ⟨996393463309711292898173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2657049235492563447728461 996393463309711292898173)
                ·
                  refine ⟨373647548741141734836815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 996393463309711292898173 373647548741141734836815)
                  ·
                    rfl

theorem cell21_1637271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3, 3].length) (baseStart_1637271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1637271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1637271 prefixEnd_1637271 := by exact prefixLift 1637271
  have htrace : WordTrace (prefixWord ++ tailWord_1637271) baseStart_1637271 baseEnd_1637271 := by
    simpa [prefixWord, tailWord_1637271, baseEnd_1637271] using wordTrace_append hprefix tailTrace_1637271
  have hstable : (prefixWord ++ tailWord_1637271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637271).length < 2 ^ (prefixWord ++ tailWord_1637271).sum := by decide
  have hdescent : baseEnd_1637271 < baseStart_1637271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637361 : List Nat := [1, 2, 2, 2, 4, 2, 1, 3, 4]
def baseStart_1637361 : Nat := 118140960795 + 1637361 * 2 ^ 59
def prefixEnd_1637361 : Nat := 4983230072969 + 3 ^ 40 * 1637361 * 2
def baseEnd_1637361 : Nat := 373668087967321578336631

theorem tailTrace_1637361 : CollatzResearch.WordTrace tailWord_1637361 prefixEnd_1637361 373668087967321578336631 := by
  unfold tailWord_1637361
  simp only [CollatzResearch.WordTrace]
  refine ⟨59719461821128210840711937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39812974547418807227141291 59719461821128210840711937)
  ·
    refine ⟨44789596365846158130533953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59719461821128210840711937 44789596365846158130533953)
    ·
      refine ⟨33592197274384618597900465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44789596365846158130533953 33592197274384618597900465)
      ·
        refine ⟨25194147955788463948425349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33592197274384618597900465 25194147955788463948425349)
        ·
          refine ⟨4723902741710336990329753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25194147955788463948425349 4723902741710336990329753)
          ·
            refine ⟨3542927056282752742747315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4723902741710336990329753 3542927056282752742747315)
            ·
              refine ⟨5314390584424129114120973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3542927056282752742747315 5314390584424129114120973)
              ·
                refine ⟨1992896469159048417795365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5314390584424129114120973 1992896469159048417795365)
                ·
                  refine ⟨373668087967321578336631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1992896469159048417795365 373668087967321578336631)
                  ·
                    rfl

theorem cell21_1637361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 4].length) (baseStart_1637361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1637361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1637361 prefixEnd_1637361 := by exact prefixLift 1637361
  have htrace : WordTrace (prefixWord ++ tailWord_1637361) baseStart_1637361 baseEnd_1637361 := by
    simpa [prefixWord, tailWord_1637361, baseEnd_1637361] using wordTrace_append hprefix tailTrace_1637361
  have hstable : (prefixWord ++ tailWord_1637361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637361).length < 2 ^ (prefixWord ++ tailWord_1637361).sum := by decide
  have hdescent : baseEnd_1637361 < baseStart_1637361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637403 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 10]
def baseStart_1637403 : Nat := 118140960795 + 1637403 * 2 ^ 59
def prefixEnd_1637403 : Nat := 4983230072969 + 3 ^ 40 * 1637403 * 2
def baseEnd_1637403 : Nat := 373677672939538838636545

theorem tailTrace_1637403 : CollatzResearch.WordTrace tailWord_1637403 prefixEnd_1637403 373677672939538838636545 := by
  unfold tailWord_1637403
  simp only [CollatzResearch.WordTrace]
  refine ⟨59720993686976052013740863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39813995791317368009160575 59720993686976052013740863)
  ·
    refine ⟨89581490530464078020611295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59720993686976052013740863 89581490530464078020611295)
    ·
      refine ⟨134372235795696117030916943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89581490530464078020611295 134372235795696117030916943)
      ·
        refine ⟨201558353693544175546375415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134372235795696117030916943 201558353693544175546375415)
        ·
          refine ⟨302337530540316263319563123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201558353693544175546375415 302337530540316263319563123)
          ·
            refine ⟨453506295810474394979344685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302337530540316263319563123 453506295810474394979344685)
            ·
              refine ⟨170064860928927898117254257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 453506295810474394979344685 170064860928927898117254257)
              ·
                refine ⟨127548645696695923587940693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170064860928927898117254257 127548645696695923587940693)
                ·
                  refine ⟨373677672939538838636545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 127548645696695923587940693 373677672939538838636545)
                  ·
                    rfl

theorem cell21_1637403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 10].length) (baseStart_1637403 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1637403 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1637403 prefixEnd_1637403 := by exact prefixLift 1637403
  have htrace : WordTrace (prefixWord ++ tailWord_1637403) baseStart_1637403 baseEnd_1637403 := by
    simpa [prefixWord, tailWord_1637403, baseEnd_1637403] using wordTrace_append hprefix tailTrace_1637403
  have hstable : (prefixWord ++ tailWord_1637403).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637403).length < 2 ^ (prefixWord ++ tailWord_1637403).sum := by decide
  have hdescent : baseEnd_1637403 < baseStart_1637403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637420 : List Nat := [2, 2, 1, 1, 1, 2, 3, 5, 4]
def baseStart_1637420 : Nat := 118140960795 + 1637420 * 2 ^ 59
def prefixEnd_1637420 : Nat := 4983230072969 + 3 ^ 40 * 1637420 * 2
def baseEnd_1637420 : Nat := 373681552571150586853177

theorem tailTrace_1637420 : CollatzResearch.WordTrace tailWord_1637420 prefixEnd_1637420 373681552571150586853177 := by
  unfold tailWord_1637420
  simp only [CollatzResearch.WordTrace]
  refine ⟨29860806863957231958554857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39814409151942975944739809 29860806863957231958554857)
  ·
    refine ⟨22395605147967923968916143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29860806863957231958554857 22395605147967923968916143)
    ·
      refine ⟨33593407721951885953374215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22395605147967923968916143 33593407721951885953374215)
      ·
        refine ⟨50390111582927828930061323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33593407721951885953374215 50390111582927828930061323)
        ·
          refine ⟨75585167374391743395091985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50390111582927828930061323 75585167374391743395091985)
          ·
            refine ⟨56688875530793807546318989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75585167374391743395091985 56688875530793807546318989)
            ·
              refine ⟨21258328324047677829869621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56688875530793807546318989 21258328324047677829869621)
              ·
                refine ⟨1992968280379469796550277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21258328324047677829869621 1992968280379469796550277)
                ·
                  refine ⟨373681552571150586853177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1992968280379469796550277 373681552571150586853177)
                  ·
                    rfl

theorem cell21_1637420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_1637420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1637420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1637420 prefixEnd_1637420 := by exact prefixLift 1637420
  have htrace : WordTrace (prefixWord ++ tailWord_1637420) baseStart_1637420 baseEnd_1637420 := by
    simpa [prefixWord, tailWord_1637420, baseEnd_1637420] using wordTrace_append hprefix tailTrace_1637420
  have hstable : (prefixWord ++ tailWord_1637420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637420).length < 2 ^ (prefixWord ++ tailWord_1637420).sum := by decide
  have hdescent : baseEnd_1637420 < baseStart_1637420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637434 : List Nat := [3, 1, 1, 1, 3, 1, 2, 9]
def baseStart_1637434 : Nat := 118140960795 + 1637434 * 2 ^ 59
def prefixEnd_1637434 : Nat := 4983230072969 + 3 ^ 40 * 1637434 * 2
def baseEnd_1637434 : Nat := 124561582520629891206605

theorem tailTrace_1637434 : CollatzResearch.WordTrace tailWord_1637434 prefixEnd_1637434 124561582520629891206605 := by
  unfold tailWord_1637434
  simp only [CollatzResearch.WordTrace]
  refine ⟨14930531087465936077029839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39814749566575829538746237 14930531087465936077029839)
  ·
    refine ⟨22395796631198904115544759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14930531087465936077029839 22395796631198904115544759)
    ·
      refine ⟨33593694946798356173317139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22395796631198904115544759 33593694946798356173317139)
      ·
        refine ⟨50390542420197534259975709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33593694946798356173317139 50390542420197534259975709)
        ·
          refine ⟨18896453407574075347490891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50390542420197534259975709 18896453407574075347490891)
          ·
            refine ⟨28344680111361113021236337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18896453407574075347490891 28344680111361113021236337)
            ·
              refine ⟨21258510083520834765927253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28344680111361113021236337 21258510083520834765927253)
              ·
                refine ⟨124561582520629891206605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21258510083520834765927253 124561582520629891206605)
                ·
                  rfl

theorem cell21_1637434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_1637434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1637434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1637434 prefixEnd_1637434 := by exact prefixLift 1637434
  have htrace : WordTrace (prefixWord ++ tailWord_1637434) baseStart_1637434 baseEnd_1637434 := by
    simpa [prefixWord, tailWord_1637434, baseEnd_1637434] using wordTrace_append hprefix tailTrace_1637434
  have hstable : (prefixWord ++ tailWord_1637434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637434).length < 2 ^ (prefixWord ++ tailWord_1637434).sum := by decide
  have hdescent : baseEnd_1637434 < baseStart_1637434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637482 : List Nat := [3, 1, 3, 2, 2, 1, 2, 2, 5]
def baseStart_1637482 : Nat := 118140960795 + 1637482 * 2 ^ 59
def prefixEnd_1637482 : Nat := 4983230072969 + 3 ^ 40 * 1637482 * 2
def baseEnd_1637482 : Nat := 373695701815852256819717

theorem tailTrace_1637482 : CollatzResearch.WordTrace tailWord_1637482 prefixEnd_1637482 373695701815852256819717 := by
  unfold tailWord_1637482
  simp only [CollatzResearch.WordTrace]
  refine ⟨14930968763422462126466675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39815916702459899003911133 14930968763422462126466675)
  ·
    refine ⟨22396453145133693189700013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14930968763422462126466675 22396453145133693189700013)
    ·
      refine ⟨8398669929425134946137505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22396453145133693189700013 8398669929425134946137505)
      ·
        refine ⟨6299002447068851209603129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8398669929425134946137505 6299002447068851209603129)
        ·
          refine ⟨4724251835301638407202347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6299002447068851209603129 4724251835301638407202347)
          ·
            refine ⟨7086377752952457610803521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4724251835301638407202347 7086377752952457610803521)
            ·
              refine ⟨5314783314714343208102641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7086377752952457610803521 5314783314714343208102641)
              ·
                refine ⟨3986087486035757406076981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5314783314714343208102641 3986087486035757406076981)
                ·
                  refine ⟨373695701815852256819717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3986087486035757406076981 373695701815852256819717)
                  ·
                    rfl

theorem cell21_1637482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_1637482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1637482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1637482 prefixEnd_1637482 := by exact prefixLift 1637482
  have htrace : WordTrace (prefixWord ++ tailWord_1637482) baseStart_1637482 baseEnd_1637482 := by
    simpa [prefixWord, tailWord_1637482, baseEnd_1637482] using wordTrace_append hprefix tailTrace_1637482
  have hstable : (prefixWord ++ tailWord_1637482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637482).length < 2 ^ (prefixWord ++ tailWord_1637482).sum := by decide
  have hdescent : baseEnd_1637482 < baseStart_1637482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637502 : List Nat := [4, 2, 4, 1, 1, 2, 7]
def baseStart_1637502 : Nat := 118140960795 + 1637502 * 2 ^ 59
def prefixEnd_1637502 : Nat := 4983230072969 + 3 ^ 40 * 1637502 * 2
def baseEnd_1637502 : Nat := 41522251787592962942927

theorem tailTrace_1637502 : CollatzResearch.WordTrace tailWord_1637502 prefixEnd_1637502 41522251787592962942927 := by
  unfold tailWord_1637502
  simp only [CollatzResearch.WordTrace]
  refine ⟨7465575564202173990199345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39816403009078261281063173 7465575564202173990199345)
  ·
    refine ⟨5599181673151630492649509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7465575564202173990199345 5599181673151630492649509)
    ·
      refine ⟨1049846563715930717371783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5599181673151630492649509 1049846563715930717371783)
      ·
        refine ⟨1574769845573896076057675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1049846563715930717371783 1574769845573896076057675)
        ·
          refine ⟨2362154768360844114086513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1574769845573896076057675 2362154768360844114086513)
          ·
            refine ⟨1771616076270633085564885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2362154768360844114086513 1771616076270633085564885)
            ·
              refine ⟨41522251787592962942927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1771616076270633085564885 41522251787592962942927)
              ·
                rfl

theorem cell21_1637502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 7].length) (baseStart_1637502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1637502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1637502 prefixEnd_1637502 := by exact prefixLift 1637502
  have htrace : WordTrace (prefixWord ++ tailWord_1637502) baseStart_1637502 baseEnd_1637502 := by
    simpa [prefixWord, tailWord_1637502, baseEnd_1637502] using wordTrace_append hprefix tailTrace_1637502
  have hstable : (prefixWord ++ tailWord_1637502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637502).length < 2 ^ (prefixWord ++ tailWord_1637502).sum := by decide
  have hdescent : baseEnd_1637502 < baseStart_1637502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637527 : List Nat := [1, 1, 3, 3, 3, 2, 2, 6]
def baseStart_1637527 : Nat := 118140960795 + 1637527 * 2 ^ 59
def prefixEnd_1637527 : Nat := 4983230072969 + 3 ^ 40 * 1637527 * 2
def baseEnd_1637527 : Nat := 124568657142980726189875

theorem tailTrace_1637527 : CollatzResearch.WordTrace tailWord_1637527 prefixEnd_1637527 124568657142980726189875 := by
  unfold tailWord_1637527
  simp only [CollatzResearch.WordTrace]
  refine ⟨59725516338526821191254835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39817010892351214127503223 59725516338526821191254835)
  ·
    refine ⟨89588274507790231786882253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59725516338526821191254835 89588274507790231786882253)
    ·
      refine ⟨33595602940421336920080845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89588274507790231786882253 33595602940421336920080845)
      ·
        refine ⟨12598351102658001345030317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33595602940421336920080845 12598351102658001345030317)
        ·
          refine ⟨4724381663496750504386369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12598351102658001345030317 4724381663496750504386369)
          ·
            refine ⟨3543286247622562878289777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4724381663496750504386369 3543286247622562878289777)
            ·
              refine ⟨2657464685716922158717333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3543286247622562878289777 2657464685716922158717333)
              ·
                refine ⟨124568657142980726189875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2657464685716922158717333 124568657142980726189875)
                ·
                  rfl

theorem cell21_1637527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 6].length) (baseStart_1637527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1637527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1637527 prefixEnd_1637527 := by exact prefixLift 1637527
  have htrace : WordTrace (prefixWord ++ tailWord_1637527) baseStart_1637527 baseEnd_1637527 := by
    simpa [prefixWord, tailWord_1637527, baseEnd_1637527] using wordTrace_append hprefix tailTrace_1637527
  have hstable : (prefixWord ++ tailWord_1637527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637527).length < 2 ^ (prefixWord ++ tailWord_1637527).sum := by decide
  have hdescent : baseEnd_1637527 < baseStart_1637527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637530 : List Nat := [3, 1, 1, 5, 1, 1, 4, 1, 4]
def baseStart_1637530 : Nat := 118140960795 + 1637530 * 2 ^ 59
def prefixEnd_1637530 : Nat := 4983230072969 + 3 ^ 40 * 1637530 * 2
def baseEnd_1637530 : Nat := 373706656069814840019619

theorem tailTrace_1637530 : CollatzResearch.WordTrace tailWord_1637530 prefixEnd_1637530 373706656069814840019619 := by
  unfold tailWord_1637530
  simp only [CollatzResearch.WordTrace]
  refine ⟨14931406439378988175903511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39817083838343968469076029 14931406439378988175903511)
  ·
    refine ⟨22397109659068482263855267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14931406439378988175903511 22397109659068482263855267)
    ·
      refine ⟨33595664488602723395782901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22397109659068482263855267 33595664488602723395782901)
      ·
        refine ⟨3149593545806505318354647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33595664488602723395782901 3149593545806505318354647)
        ·
          refine ⟨4724390318709757977531971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3149593545806505318354647 4724390318709757977531971)
          ·
            refine ⟨7086585478064636966297957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4724390318709757977531971 7086585478064636966297957)
            ·
              refine ⟨1328734777137119431180867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7086585478064636966297957 1328734777137119431180867)
              ·
                refine ⟨1993102165705679146771301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1328734777137119431180867 1993102165705679146771301)
                ·
                  refine ⟨373706656069814840019619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1993102165705679146771301 373706656069814840019619)
                  ·
                    rfl

theorem cell21_1637530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_1637530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1637530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1637530 prefixEnd_1637530 := by exact prefixLift 1637530
  have htrace : WordTrace (prefixWord ++ tailWord_1637530) baseStart_1637530 baseEnd_1637530 := by
    simpa [prefixWord, tailWord_1637530, baseEnd_1637530] using wordTrace_append hprefix tailTrace_1637530
  have hstable : (prefixWord ++ tailWord_1637530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637530).length < 2 ^ (prefixWord ++ tailWord_1637530).sum := by decide
  have hdescent : baseEnd_1637530 < baseStart_1637530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637555 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 8]
def baseStart_1637555 : Nat := 118140960795 + 1637555 * 2 ^ 59
def prefixEnd_1637555 : Nat := 4983230072969 + 3 ^ 40 * 1637555 * 2
def baseEnd_1637555 : Nat := 373712361410420352102901

theorem tailTrace_1637555 : CollatzResearch.WordTrace tailWord_1637555 prefixEnd_1637555 373712361410420352102901 := by
  unfold tailWord_1637555
  simp only [CollatzResearch.WordTrace]
  refine ⟨59726537582425381973274119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39817691721616921315516079 59726537582425381973274119)
  ·
    refine ⟨89589806373638072959911179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59726537582425381973274119 89589806373638072959911179)
    ·
      refine ⟨134384709560457109439866769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89589806373638072959911179 134384709560457109439866769)
      ·
        refine ⟨100788532170342832079900077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134384709560457109439866769 100788532170342832079900077)
        ·
          refine ⟨37795699563878562029962529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100788532170342832079900077 37795699563878562029962529)
          ·
            refine ⟨28346774672908921522471897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37795699563878562029962529 28346774672908921522471897)
            ·
              refine ⟨21260081004681691141853923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28346774672908921522471897 21260081004681691141853923)
              ·
                refine ⟨31890121507022536712780885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21260081004681691141853923 31890121507022536712780885)
                ·
                  refine ⟨373712361410420352102901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31890121507022536712780885 373712361410420352102901)
                  ·
                    rfl

theorem cell21_1637555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 8].length) (baseStart_1637555 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1637555 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1637555 prefixEnd_1637555 := by exact prefixLift 1637555
  have htrace : WordTrace (prefixWord ++ tailWord_1637555) baseStart_1637555 baseEnd_1637555 := by
    simpa [prefixWord, tailWord_1637555, baseEnd_1637555] using wordTrace_append hprefix tailTrace_1637555
  have hstable : (prefixWord ++ tailWord_1637555).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637555).length < 2 ^ (prefixWord ++ tailWord_1637555).sum := by decide
  have hdescent : baseEnd_1637555 < baseStart_1637555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637589 : List Nat := [1, 3, 2, 4, 1, 1, 2, 3, 4]
def baseStart_1637589 : Nat := 118140960795 + 1637589 * 2 ^ 59
def prefixEnd_1637589 : Nat := 4983230072969 + 3 ^ 40 * 1637589 * 2
def baseEnd_1637589 : Nat := 373720120673643848536165

theorem tailTrace_1637589 : CollatzResearch.WordTrace tailWord_1637589 prefixEnd_1637589 373720120673643848536165 := by
  unfold tailWord_1637589
  simp only [CollatzResearch.WordTrace]
  refine ⟨59727777664302205780011821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39818518442868137186674547 59727777664302205780011821)
  ·
    refine ⟨22397916624113327167504433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59727777664302205780011821 22397916624113327167504433)
    ·
      refine ⟨16798437468084995375628325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22397916624113327167504433 16798437468084995375628325)
      ·
        refine ⟨3149707025265936632930311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16798437468084995375628325 3149707025265936632930311)
        ·
          refine ⟨4724560537898904949395467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3149707025265936632930311 4724560537898904949395467)
          ·
            refine ⟨7086840806848357424093201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4724560537898904949395467 7086840806848357424093201)
            ·
              refine ⟨5315130605136268068069901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7086840806848357424093201 5315130605136268068069901)
              ·
                refine ⟨1993173976926100525526213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5315130605136268068069901 1993173976926100525526213)
                ·
                  refine ⟨373720120673643848536165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1993173976926100525526213 373720120673643848536165)
                  ·
                    rfl

theorem cell21_1637589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_1637589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1637589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1637589 prefixEnd_1637589 := by exact prefixLift 1637589
  have htrace : WordTrace (prefixWord ++ tailWord_1637589) baseStart_1637589 baseEnd_1637589 := by
    simpa [prefixWord, tailWord_1637589, baseEnd_1637589] using wordTrace_append hprefix tailTrace_1637589
  have hstable : (prefixWord ++ tailWord_1637589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637589).length < 2 ^ (prefixWord ++ tailWord_1637589).sum := by decide
  have hdescent : baseEnd_1637589 < baseStart_1637589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637738 : List Nat := [3, 1, 3, 3, 11]
def baseStart_1637738 : Nat := 118140960795 + 1637738 * 2 ^ 59
def prefixEnd_1637738 : Nat := 4983230072969 + 3 ^ 40 * 1637738 * 2
def baseEnd_1637738 : Nat := 4614248450662379019167

theorem tailTrace_1637738 : CollatzResearch.WordTrace tailWord_1637738 prefixEnd_1637738 4614248450662379019167 := by
  unfold tailWord_1637738
  simp only [CollatzResearch.WordTrace]
  refine ⟨14933303035190601056796467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39822141427174936151457245 14933303035190601056796467)
  ·
    refine ⟨22399954552785901585194701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14933303035190601056796467 22399954552785901585194701)
    ·
      refine ⟨8399982957294713094448013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22399954552785901585194701 8399982957294713094448013)
      ·
        refine ⟨3149993608985517410418005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8399982957294713094448013 3149993608985517410418005)
        ·
          refine ⟨4614248450662379019167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3149993608985517410418005 4614248450662379019167)
          ·
            rfl

theorem cell21_1637738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 11].length) (baseStart_1637738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1637738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1637738 prefixEnd_1637738 := by exact prefixLift 1637738
  have htrace : WordTrace (prefixWord ++ tailWord_1637738) baseStart_1637738 baseEnd_1637738 := by
    simpa [prefixWord, tailWord_1637738, baseEnd_1637738] using wordTrace_append hprefix tailTrace_1637738
  have hstable : (prefixWord ++ tailWord_1637738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637738).length < 2 ^ (prefixWord ++ tailWord_1637738).sum := by decide
  have hdescent : baseEnd_1637738 < baseStart_1637738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637741 : List Nat := [1, 5, 1, 1, 1, 4, 2, 2, 4]
def baseStart_1637741 : Nat := 118140960795 + 1637741 * 2 ^ 59
def prefixEnd_1637741 : Nat := 4983230072969 + 3 ^ 40 * 1637741 * 2
def baseEnd_1637741 : Nat := 373754809144525362002521

theorem tailTrace_1637741 : CollatzResearch.WordTrace tailWord_1637741 prefixEnd_1637741 373754809144525362002521 := by
  unfold tailWord_1637741
  simp only [CollatzResearch.WordTrace]
  refine ⟨59733321559751535739545077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39822214373167690493030051 59733321559751535739545077)
  ·
    refine ⟨5599998896226706475582351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59733321559751535739545077 5599998896226706475582351)
    ·
      refine ⟨8399998344340059713373527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5599998896226706475582351 8399998344340059713373527)
      ·
        refine ⟨12599997516510089570060291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8399998344340059713373527 12599997516510089570060291)
        ·
          refine ⟨18899996274765134355090437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12599997516510089570060291 18899996274765134355090437)
          ·
            refine ⟨3543749301518462691579457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18899996274765134355090437 3543749301518462691579457)
            ·
              refine ⟨2657811976138847018684593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3543749301518462691579457 2657811976138847018684593)
              ·
                refine ⟨1993358982104135264013445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2657811976138847018684593 1993358982104135264013445)
                ·
                  refine ⟨373754809144525362002521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1993358982104135264013445 373754809144525362002521)
                  ·
                    rfl

theorem cell21_1637741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_1637741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1637741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1637741 prefixEnd_1637741 := by exact prefixLift 1637741
  have htrace : WordTrace (prefixWord ++ tailWord_1637741) baseStart_1637741 baseEnd_1637741 := by
    simpa [prefixWord, tailWord_1637741, baseEnd_1637741] using wordTrace_append hprefix tailTrace_1637741
  have hstable : (prefixWord ++ tailWord_1637741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637741).length < 2 ^ (prefixWord ++ tailWord_1637741).sum := by decide
  have hdescent : baseEnd_1637741 < baseStart_1637741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637752 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 11]
def baseStart_1637752 : Nat := 118140960795 + 1637752 * 2 ^ 59
def prefixEnd_1637752 : Nat := 4983230072969 + 3 ^ 40 * 1637752 * 2
def baseEnd_1637752 : Nat := 373757319494391787319165

theorem tailTrace_1637752 : CollatzResearch.WordTrace tailWord_1637752 prefixEnd_1637752 373757319494391787319165 := by
  unfold tailWord_1637752
  simp only [CollatzResearch.WordTrace]
  refine ⟨29866861381355842309097755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39822481841807789745463673 29866861381355842309097755)
  ·
    refine ⟨44800292072033763463646633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29866861381355842309097755 44800292072033763463646633)
    ·
      refine ⟨33600219054025322597734975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44800292072033763463646633 33600219054025322597734975)
      ·
        refine ⟨50400328581037983896602463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33600219054025322597734975 50400328581037983896602463)
        ·
          refine ⟨75600492871556975844903695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50400328581037983896602463 75600492871556975844903695)
          ·
            refine ⟨113400739307335463767355543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75600492871556975844903695 113400739307335463767355543)
            ·
              refine ⟨170101108961003195651033315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113400739307335463767355543 170101108961003195651033315)
              ·
                refine ⟨255151663441504793476549973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170101108961003195651033315 255151663441504793476549973)
                ·
                  refine ⟨373757319494391787319165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 255151663441504793476549973 373757319494391787319165)
                  ·
                    rfl

theorem cell21_1637752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_1637752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1637752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1637752 prefixEnd_1637752 := by exact prefixLift 1637752
  have htrace : WordTrace (prefixWord ++ tailWord_1637752) baseStart_1637752 baseEnd_1637752 := by
    simpa [prefixWord, tailWord_1637752, baseEnd_1637752] using wordTrace_append hprefix tailTrace_1637752
  have hstable : (prefixWord ++ tailWord_1637752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637752).length < 2 ^ (prefixWord ++ tailWord_1637752).sum := by decide
  have hdescent : baseEnd_1637752 < baseStart_1637752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637783 : List Nat := [1, 1, 3, 3, 1, 1, 1, 4, 6]
def baseStart_1637783 : Nat := 118140960795 + 1637783 * 2 ^ 59
def prefixEnd_1637783 : Nat := 4983230072969 + 3 ^ 40 * 1637783 * 2
def baseEnd_1637783 : Nat := 373764394116742622302435

theorem tailTrace_1637783 : CollatzResearch.WordTrace tailWord_1637783 prefixEnd_1637783 373764394116742622302435 := by
  unfold tailWord_1637783
  simp only [CollatzResearch.WordTrace]
  refine ⟨59734853425599376912574003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39823235617066251275049335 59734853425599376912574003)
  ·
    refine ⟨89602280138399065368861005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59734853425599376912574003 89602280138399065368861005)
    ·
      refine ⟨33600855051899649513322877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89602280138399065368861005 33600855051899649513322877)
      ·
        refine ⟨12600320644462368567496079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33600855051899649513322877 12600320644462368567496079)
        ·
          refine ⟨18900480966693552851244119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12600320644462368567496079 18900480966693552851244119)
          ·
            refine ⟨28350721450040329276866179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18900480966693552851244119 28350721450040329276866179)
            ·
              refine ⟨42526082175060493915299269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28350721450040329276866179 42526082175060493915299269)
              ·
                refine ⟨7973640407823842609118613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42526082175060493915299269 7973640407823842609118613)
                ·
                  refine ⟨373764394116742622302435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7973640407823842609118613 373764394116742622302435)
                  ·
                    rfl

theorem cell21_1637783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 6].length) (baseStart_1637783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1637783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1637783 prefixEnd_1637783 := by exact prefixLift 1637783
  have htrace : WordTrace (prefixWord ++ tailWord_1637783) baseStart_1637783 baseEnd_1637783 := by
    simpa [prefixWord, tailWord_1637783, baseEnd_1637783] using wordTrace_append hprefix tailTrace_1637783
  have hstable : (prefixWord ++ tailWord_1637783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637783).length < 2 ^ (prefixWord ++ tailWord_1637783).sum := by decide
  have hdescent : baseEnd_1637783 < baseStart_1637783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638025 : List Nat := [1, 2, 1, 1, 4, 1, 11]
def baseStart_1638025 : Nat := 118140960795 + 1638025 * 2 ^ 59
def prefixEnd_1638025 : Nat := 4983230072969 + 3 ^ 40 * 1638025 * 2
def baseEnd_1638025 : Nat := 41535513534867108807623

theorem tailTrace_1638025 : CollatzResearch.WordTrace tailWord_1638025 prefixEnd_1638025 41535513534867108807623 := by
  unfold tailWord_1638025
  simp only [CollatzResearch.WordTrace]
  refine ⟨59743679890722652242883529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39829119927148434828589019 59743679890722652242883529)
  ·
    refine ⟨44807759918041989182162647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59743679890722652242883529 44807759918041989182162647)
    ·
      refine ⟨67211639877062983773243971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44807759918041989182162647 67211639877062983773243971)
      ·
        refine ⟨100817459815594475659865957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67211639877062983773243971 100817459815594475659865957)
        ·
          refine ⟨18903273715423964186224867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100817459815594475659865957 18903273715423964186224867)
          ·
            refine ⟨28354910573135946279337301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18903273715423964186224867 28354910573135946279337301)
            ·
              refine ⟨41535513534867108807623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 28354910573135946279337301 41535513534867108807623)
              ·
                rfl

theorem cell21_1638025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 11].length) (baseStart_1638025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1638025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1638025 prefixEnd_1638025 := by exact prefixLift 1638025
  have htrace : WordTrace (prefixWord ++ tailWord_1638025) baseStart_1638025 baseEnd_1638025 := by
    simpa [prefixWord, tailWord_1638025, baseEnd_1638025] using wordTrace_append hprefix tailTrace_1638025
  have hstable : (prefixWord ++ tailWord_1638025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638025).length < 2 ^ (prefixWord ++ tailWord_1638025).sum := by decide
  have hdescent : baseEnd_1638025 < baseStart_1638025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638194 : List Nat := [3, 2, 1, 1, 3, 4, 7]
def baseStart_1638194 : Nat := 118140960795 + 1638194 * 2 ^ 59
def prefixEnd_1638194 : Nat := 4983230072969 + 3 ^ 40 * 1638194 * 2
def baseEnd_1638194 : Nat := 41539798879588582327955

theorem tailTrace_1638194 : CollatzResearch.WordTrace tailWord_1638194 prefixEnd_1638194 41539798879588582327955 := by
  unfold tailWord_1638194
  simp only [CollatzResearch.WordTrace]
  refine ⟨14937460956777598526446409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39833229218073596070523757 14937460956777598526446409)
  ·
    refine ⟨11203095717583198894834807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14937460956777598526446409 11203095717583198894834807)
    ·
      refine ⟨16804643576374798342252211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11203095717583198894834807 16804643576374798342252211)
      ·
        refine ⟨25206965364562197513378317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16804643576374798342252211 25206965364562197513378317)
        ·
          refine ⟨9452612011710824067516869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25206965364562197513378317 9452612011710824067516869)
          ·
            refine ⟨1772364752195779512659413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9452612011710824067516869 1772364752195779512659413)
            ·
              refine ⟨41539798879588582327955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1772364752195779512659413 41539798879588582327955)
              ·
                rfl

theorem cell21_1638194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 7].length) (baseStart_1638194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1638194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1638194 prefixEnd_1638194 := by exact prefixLift 1638194
  have htrace : WordTrace (prefixWord ++ tailWord_1638194) baseStart_1638194 baseEnd_1638194 := by
    simpa [prefixWord, tailWord_1638194, baseEnd_1638194] using wordTrace_append hprefix tailTrace_1638194
  have hstable : (prefixWord ++ tailWord_1638194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638194).length < 2 ^ (prefixWord ++ tailWord_1638194).sum := by decide
  have hdescent : baseEnd_1638194 < baseStart_1638194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638214 : List Nat := [6, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_1638214 : Nat := 118140960795 + 1638214 * 2 ^ 59
def prefixEnd_1638214 : Nat := 4983230072969 + 3 ^ 40 * 1638214 * 2
def baseEnd_1638214 : Nat := 373862754188781650618221

theorem tailTrace_1638214 : CollatzResearch.WordTrace tailWord_1638214 prefixEnd_1638214 373862754188781650618221 := by
  unfold tailWord_1638214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1867205415219935547547303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39833715524691958347675797 1867205415219935547547303)
  ·
    refine ⟨2800808122829903321320955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1867205415219935547547303 2800808122829903321320955)
    ·
      refine ⟨4201212184244854981981433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2800808122829903321320955 4201212184244854981981433)
      ·
        refine ⟨3150909138183641236486075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4201212184244854981981433 3150909138183641236486075)
        ·
          refine ⟨4726363707275461854729113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3150909138183641236486075 4726363707275461854729113)
          ·
            refine ⟨3544772780456596391046835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4726363707275461854729113 3544772780456596391046835)
            ·
              refine ⟨5317159170684894586570253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3544772780456596391046835 5317159170684894586570253)
              ·
                refine ⟨1993934689006835469963845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5317159170684894586570253 1993934689006835469963845)
                ·
                  refine ⟨373862754188781650618221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1993934689006835469963845 373862754188781650618221)
                  ·
                    rfl

theorem cell21_1638214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_1638214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1638214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1638214 prefixEnd_1638214 := by exact prefixLift 1638214
  have htrace : WordTrace (prefixWord ++ tailWord_1638214) baseStart_1638214 baseEnd_1638214 := by
    simpa [prefixWord, tailWord_1638214, baseEnd_1638214] using wordTrace_append hprefix tailTrace_1638214
  have hstable : (prefixWord ++ tailWord_1638214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638214).length < 2 ^ (prefixWord ++ tailWord_1638214).sum := by decide
  have hdescent : baseEnd_1638214 < baseStart_1638214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638329 : List Nat := [1, 2, 1, 4, 2, 1, 2, 8]
def baseStart_1638329 : Nat := 118140960795 + 1638329 * 2 ^ 59
def prefixEnd_1638329 : Nat := 4983230072969 + 3 ^ 40 * 1638329 * 2
def baseEnd_1638329 : Nat := 124629666251855668733773

theorem tailTrace_1638329 : CollatzResearch.WordTrace tailWord_1638329 prefixEnd_1638329 124629666251855668733773 := by
  unfold tailWord_1638329
  simp only [CollatzResearch.WordTrace]
  refine ⟨59754767681621312161950041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39836511787747541441300027 59754767681621312161950041)
  ·
    refine ⟨44816075761215984121462531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59754767681621312161950041 44816075761215984121462531)
    ·
      refine ⟨67224113641823976182193797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44816075761215984121462531 67224113641823976182193797)
      ·
        refine ⟨12604521307841995534161337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67224113641823976182193797 12604521307841995534161337)
        ·
          refine ⟨9453390980881496650621003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12604521307841995534161337 9453390980881496650621003)
          ·
            refine ⟨14180086471322244975931505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9453390980881496650621003 14180086471322244975931505)
            ·
              refine ⟨10635064853491683731948629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14180086471322244975931505 10635064853491683731948629)
              ·
                refine ⟨124629666251855668733773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10635064853491683731948629 124629666251855668733773)
                ·
                  rfl

theorem cell21_1638329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 8].length) (baseStart_1638329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1638329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1638329 prefixEnd_1638329 := by exact prefixLift 1638329
  have htrace : WordTrace (prefixWord ++ tailWord_1638329) baseStart_1638329 baseEnd_1638329 := by
    simpa [prefixWord, tailWord_1638329, baseEnd_1638329] using wordTrace_append hprefix tailTrace_1638329
  have hstable : (prefixWord ++ tailWord_1638329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638329).length < 2 ^ (prefixWord ++ tailWord_1638329).sum := by decide
  have hdescent : baseEnd_1638329 < baseStart_1638329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638346 : List Nat := [3, 1, 2, 1, 2, 1, 6, 5]
def baseStart_1638346 : Nat := 118140960795 + 1638346 * 2 ^ 59
def prefixEnd_1638346 : Nat := 4983230072969 + 3 ^ 40 * 1638346 * 2
def baseEnd_1638346 : Nat := 124630959462392918139317

theorem tailTrace_1638346 : CollatzResearch.WordTrace tailWord_1638346 prefixEnd_1638346 124630959462392918139317 := by
  unfold tailWord_1638346
  simp only [CollatzResearch.WordTrace]
  refine ⟨14938846930639931016329723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39836925148373149376879261 14938846930639931016329723)
  ·
    refine ⟨22408270395959896524494585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14938846930639931016329723 22408270395959896524494585)
    ·
      refine ⟨16806202796969922393370939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22408270395959896524494585 16806202796969922393370939)
      ·
        refine ⟨25209304195454883590056409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16806202796969922393370939 25209304195454883590056409)
        ·
          refine ⟨18906978146591162692542307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25209304195454883590056409 18906978146591162692542307)
          ·
            refine ⟨28360467219886744038813461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18906978146591162692542307 28360467219886744038813461)
            ·
              refine ⟨1329396900932191126819381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28360467219886744038813461 1329396900932191126819381)
              ·
                refine ⟨124630959462392918139317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1329396900932191126819381 124630959462392918139317)
                ·
                  rfl

theorem cell21_1638346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 5].length) (baseStart_1638346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1638346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1638346 prefixEnd_1638346 := by exact prefixLift 1638346
  have htrace : WordTrace (prefixWord ++ tailWord_1638346) baseStart_1638346 baseEnd_1638346 := by
    simpa [prefixWord, tailWord_1638346, baseEnd_1638346] using wordTrace_append hprefix tailTrace_1638346
  have hstable : (prefixWord ++ tailWord_1638346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638346).length < 2 ^ (prefixWord ++ tailWord_1638346).sum := by decide
  have hdescent : baseEnd_1638346 < baseStart_1638346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638405 : List Nat := [1, 3, 1, 1, 2, 4, 2, 7]
def baseStart_1638405 : Nat := 118140960795 + 1638405 * 2 ^ 59
def prefixEnd_1638405 : Nat := 4983230072969 + 3 ^ 40 * 1638405 * 2
def baseEnd_1638405 : Nat := 124635447663669254311499

theorem tailTrace_1638405 : CollatzResearch.WordTrace tailWord_1638405 prefixEnd_1638405 124635447663669254311499 := by
  unfold tailWord_1638405
  simp only [CollatzResearch.WordTrace]
  refine ⟨59757539629345977141716669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39838359752897318094477779 59757539629345977141716669)
  ·
    refine ⟨22409077361004741428143751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59757539629345977141716669 22409077361004741428143751)
    ·
      refine ⟨33613616041507112142215627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22409077361004741428143751 33613616041507112142215627)
      ·
        refine ⟨50420424062260668213323441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33613616041507112142215627 50420424062260668213323441)
        ·
          refine ⟨37815318046695501159992581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50420424062260668213323441 37815318046695501159992581)
          ·
            refine ⟨7090372133755406467498609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37815318046695501159992581 7090372133755406467498609)
            ·
              refine ⟨5317779100316554850623957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7090372133755406467498609 5317779100316554850623957)
              ·
                refine ⟨124635447663669254311499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5317779100316554850623957 124635447663669254311499)
                ·
                  rfl

theorem cell21_1638405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 7].length) (baseStart_1638405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1638405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1638405 prefixEnd_1638405 := by exact prefixLift 1638405
  have htrace : WordTrace (prefixWord ++ tailWord_1638405) baseStart_1638405 baseEnd_1638405 := by
    simpa [prefixWord, tailWord_1638405, baseEnd_1638405] using wordTrace_append hprefix tailTrace_1638405
  have hstable : (prefixWord ++ tailWord_1638405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638405).length < 2 ^ (prefixWord ++ tailWord_1638405).sum := by decide
  have hdescent : baseEnd_1638405 < baseStart_1638405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638512 : List Nat := [2, 1, 1, 1, 5, 2, 2, 2, 5]
def baseStart_1638512 : Nat := 118140960795 + 1638512 * 2 ^ 59
def prefixEnd_1638512 : Nat := 4983230072969 + 3 ^ 40 * 1638512 * 2
def baseEnd_1638512 : Nat := 373930761848799354650945

theorem tailTrace_1638512 : CollatzResearch.WordTrace tailWord_1638512 prefixEnd_1638512 373930761848799354650945 := by
  unfold tailWord_1638512
  simp only [CollatzResearch.WordTrace]
  refine ⟨29880721119979167207930895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39840961493305556277241193 29880721119979167207930895)
  ·
    refine ⟨44821081679968750811896343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29880721119979167207930895 44821081679968750811896343)
    ·
      refine ⟨67231622519953126217844515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44821081679968750811896343 67231622519953126217844515)
      ·
        refine ⟨100847433779929689326766773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67231622519953126217844515 100847433779929689326766773)
        ·
          refine ⟨9454446916868408374384385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100847433779929689326766773 9454446916868408374384385)
          ·
            refine ⟨7090835187651306280788289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9454446916868408374384385 7090835187651306280788289)
            ·
              refine ⟨5318126390738479710591217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7090835187651306280788289 5318126390738479710591217)
              ·
                refine ⟨3988594793053859782943413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5318126390738479710591217 3988594793053859782943413)
                ·
                  refine ⟨373930761848799354650945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3988594793053859782943413 373930761848799354650945)
                  ·
                    rfl

theorem cell21_1638512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 5].length) (baseStart_1638512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1638512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1638512 prefixEnd_1638512 := by exact prefixLift 1638512
  have htrace : WordTrace (prefixWord ++ tailWord_1638512) baseStart_1638512 baseEnd_1638512 := by
    simpa [prefixWord, tailWord_1638512, baseEnd_1638512] using wordTrace_append hprefix tailTrace_1638512
  have hstable : (prefixWord ++ tailWord_1638512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638512).length < 2 ^ (prefixWord ++ tailWord_1638512).sum := by decide
  have hdescent : baseEnd_1638512 < baseStart_1638512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638557 : List Nat := [1, 4, 2, 1, 1, 3, 1, 8]
def baseStart_1638557 : Nat := 118140960795 + 1638557 * 2 ^ 59
def prefixEnd_1638557 : Nat := 4983230072969 + 3 ^ 40 * 1638557 * 2
def baseEnd_1638557 : Nat := 124647010487296425466951

theorem tailTrace_1638557 : CollatzResearch.WordTrace tailWord_1638557 prefixEnd_1638557 124647010487296425466951 := by
  unfold tailWord_1638557
  simp only [CollatzResearch.WordTrace]
  refine ⟨59763083524795307101249925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39842055683196871400833283 59763083524795307101249925)
  ·
    refine ⟨11205578160899120081484361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59763083524795307101249925 11205578160899120081484361)
    ·
      refine ⟨8404183620674340061113271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11205578160899120081484361 8404183620674340061113271)
      ·
        refine ⟨12606275431011510091669907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8404183620674340061113271 12606275431011510091669907)
        ·
          refine ⟨18909413146517265137504861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12606275431011510091669907 18909413146517265137504861)
          ·
            refine ⟨7091029929943974426564323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18909413146517265137504861 7091029929943974426564323)
            ·
              refine ⟨10636544894915961639846485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7091029929943974426564323 10636544894915961639846485)
              ·
                refine ⟨124647010487296425466951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10636544894915961639846485 124647010487296425466951)
                ·
                  rfl

theorem cell21_1638557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 8].length) (baseStart_1638557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1638557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1638557 prefixEnd_1638557 := by exact prefixLift 1638557
  have htrace : WordTrace (prefixWord ++ tailWord_1638557) baseStart_1638557 baseEnd_1638557 := by
    simpa [prefixWord, tailWord_1638557, baseEnd_1638557] using wordTrace_append hprefix tailTrace_1638557
  have hstable : (prefixWord ++ tailWord_1638557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638557).length < 2 ^ (prefixWord ++ tailWord_1638557).sum := by decide
  have hdescent : baseEnd_1638557 < baseStart_1638557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638560 : List Nat := [2, 1, 1, 4, 2, 2, 4, 1, 4]
def baseStart_1638560 : Nat := 118140960795 + 1638560 * 2 ^ 59
def prefixEnd_1638560 : Nat := 4983230072969 + 3 ^ 40 * 1638560 * 2
def baseEnd_1638560 : Nat := 373941716102761937850847

theorem tailTrace_1638560 : CollatzResearch.WordTrace tailWord_1638560 prefixEnd_1638560 373941716102761937850847 := by
  unfold tailWord_1638560
  simp only [CollatzResearch.WordTrace]
  refine ⟨29881596471892219306804567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39842128629189625742406089 29881596471892219306804567)
  ·
    refine ⟨44822394707838328960206851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29881596471892219306804567 44822394707838328960206851)
    ·
      refine ⟨67233592061757493440310277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44822394707838328960206851 67233592061757493440310277)
      ·
        refine ⟨12606298511579530020058177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67233592061757493440310277 12606298511579530020058177)
        ·
          refine ⟨9454723883684647515043633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12606298511579530020058177 9454723883684647515043633)
          ·
            refine ⟨7091042912763485636282725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9454723883684647515043633 7091042912763485636282725)
            ·
              refine ⟨1329570546143153556803011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7091042912763485636282725 1329570546143153556803011)
              ·
                refine ⟨1994355819214730335204517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1329570546143153556803011 1994355819214730335204517)
                ·
                  refine ⟨373941716102761937850847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1994355819214730335204517 373941716102761937850847)
                  ·
                    rfl

theorem cell21_1638560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 4].length) (baseStart_1638560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1638560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1638560 prefixEnd_1638560 := by exact prefixLift 1638560
  have htrace : WordTrace (prefixWord ++ tailWord_1638560) baseStart_1638560 baseEnd_1638560 := by
    simpa [prefixWord, tailWord_1638560, baseEnd_1638560] using wordTrace_append hprefix tailTrace_1638560
  have hstable : (prefixWord ++ tailWord_1638560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638560).length < 2 ^ (prefixWord ++ tailWord_1638560).sum := by decide
  have hdescent : baseEnd_1638560 < baseStart_1638560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638594 : List Nat := [3, 5, 1, 1, 1, 2, 2, 2, 4]
def baseStart_1638594 : Nat := 118140960795 + 1638594 * 2 ^ 59
def prefixEnd_1638594 : Nat := 4983230072969 + 3 ^ 40 * 1638594 * 2
def baseEnd_1638594 : Nat := 373949475365985434284111

theorem tailTrace_1638594 : CollatzResearch.WordTrace tailWord_1638594 prefixEnd_1638594 373949475365985434284111 := by
  unfold tailWord_1638594
  simp only [CollatzResearch.WordTrace]
  refine ⟨14941108256415315605086709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39842955350440841613564557 14941108256415315605086709)
  ·
    refine ⟨1400728899038935837976879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14941108256415315605086709 1400728899038935837976879)
    ·
      refine ⟨2101093348558403756965319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1400728899038935837976879 2101093348558403756965319)
      ·
        refine ⟨3151640022837605635447979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2101093348558403756965319 3151640022837605635447979)
        ·
          refine ⟨4727460034256408453171969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3151640022837605635447979 4727460034256408453171969)
          ·
            refine ⟨3545595025692306339878977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4727460034256408453171969 3545595025692306339878977)
            ·
              refine ⟨2659196269269229754909233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3545595025692306339878977 2659196269269229754909233)
              ·
                refine ⟨1994397201951922316181925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2659196269269229754909233 1994397201951922316181925)
                ·
                  refine ⟨373949475365985434284111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1994397201951922316181925 373949475365985434284111)
                  ·
                    rfl

theorem cell21_1638594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_1638594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1638594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1638594 prefixEnd_1638594 := by exact prefixLift 1638594
  have htrace : WordTrace (prefixWord ++ tailWord_1638594) baseStart_1638594 baseEnd_1638594 := by
    simpa [prefixWord, tailWord_1638594, baseEnd_1638594] using wordTrace_append hprefix tailTrace_1638594
  have hstable : (prefixWord ++ tailWord_1638594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638594).length < 2 ^ (prefixWord ++ tailWord_1638594).sum := by decide
  have hdescent : baseEnd_1638594 < baseStart_1638594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638664 : List Nat := [2, 1, 3, 2, 3, 1, 1, 3, 5]
def baseStart_1638664 : Nat := 118140960795 + 1638664 * 2 ^ 59
def prefixEnd_1638664 : Nat := 4983230072969 + 3 ^ 40 * 1638664 * 2
def baseEnd_1638664 : Nat := 373965450319680868117301

theorem tailTrace_1638664 : CollatzResearch.WordTrace tailWord_1638664 prefixEnd_1638664 373965450319680868117301 := by
  unfold tailWord_1638664
  simp only [CollatzResearch.WordTrace]
  refine ⟨29883493067703832187697523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39844657423605109583596697 29883493067703832187697523)
  ·
    refine ⟨44825239601555748281546285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29883493067703832187697523 44825239601555748281546285)
    ·
      refine ⟨16809464850583405605579857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44825239601555748281546285 16809464850583405605579857)
      ·
        refine ⟨12607098637937554204184893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16809464850583405605579857 12607098637937554204184893)
        ·
          refine ⟨4727661989226582826569335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12607098637937554204184893 4727661989226582826569335)
          ·
            refine ⟨7091492983839874239854003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4727661989226582826569335 7091492983839874239854003)
            ·
              refine ⟨10637239475759811359781005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7091492983839874239854003 10637239475759811359781005)
              ·
                refine ⟨3988964803409929259917877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10637239475759811359781005 3988964803409929259917877)
                ·
                  refine ⟨373965450319680868117301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3988964803409929259917877 373965450319680868117301)
                  ·
                    rfl

theorem cell21_1638664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 5].length) (baseStart_1638664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1638664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1638664 prefixEnd_1638664 := by exact prefixLift 1638664
  have htrace : WordTrace (prefixWord ++ tailWord_1638664) baseStart_1638664 baseEnd_1638664 := by
    simpa [prefixWord, tailWord_1638664, baseEnd_1638664] using wordTrace_append hprefix tailTrace_1638664
  have hstable : (prefixWord ++ tailWord_1638664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638664).length < 2 ^ (prefixWord ++ tailWord_1638664).sum := by decide
  have hdescent : baseEnd_1638664 < baseStart_1638664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638768 : List Nat := [2, 1, 1, 1, 4, 12]
def baseStart_1638768 : Nat := 118140960795 + 1638768 * 2 ^ 59
def prefixEnd_1638768 : Nat := 4983230072969 + 3 ^ 40 * 1638768 * 2
def baseEnd_1638768 : Nat := 13851451279133325866065

theorem tailTrace_1638768 : CollatzResearch.WordTrace tailWord_1638768 prefixEnd_1638768 13851451279133325866065 := by
  unfold tailWord_1638768
  simp only [CollatzResearch.WordTrace]
  refine ⟨29885389663515445068590479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39847186218020593424787305 29885389663515445068590479)
  ·
    refine ⟨44828084495273167602885719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29885389663515445068590479 44828084495273167602885719)
    ·
      refine ⟨67242126742909751404328579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44828084495273167602885719 67242126742909751404328579)
      ·
        refine ⟨100863190114364627106492869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67242126742909751404328579 100863190114364627106492869)
        ·
          refine ⟨18911848146443367582467413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100863190114364627106492869 18911848146443367582467413)
          ·
            refine ⟨13851451279133325866065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 18911848146443367582467413 13851451279133325866065)
            ·
              rfl

theorem cell21_1638768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 12].length) (baseStart_1638768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1638768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1638768 prefixEnd_1638768 := by exact prefixLift 1638768
  have htrace : WordTrace (prefixWord ++ tailWord_1638768) baseStart_1638768 baseEnd_1638768 := by
    simpa [prefixWord, tailWord_1638768, baseEnd_1638768] using wordTrace_append hprefix tailTrace_1638768
  have hstable : (prefixWord ++ tailWord_1638768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638768).length < 2 ^ (prefixWord ++ tailWord_1638768).sum := by decide
  have hdescent : baseEnd_1638768 < baseStart_1638768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638833 : List Nat := [1, 2, 2, 4, 1, 2, 2, 4, 3]
def baseStart_1638833 : Nat := 118140960795 + 1638833 * 2 ^ 59
def prefixEnd_1638833 : Nat := 4983230072969 + 3 ^ 40 * 1638833 * 2
def baseEnd_1638833 : Nat := 374004018422174129800289

theorem tailTrace_1638833 : CollatzResearch.WordTrace tailWord_1638833 prefixEnd_1638833 374004018422174129800289 := by
  unfold tailWord_1638833
  simp only [CollatzResearch.WordTrace]
  refine ⟨59773150071795406238297153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39848766714530270825531435 59773150071795406238297153)
  ·
    refine ⟨44829862553846554678722865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59773150071795406238297153 44829862553846554678722865)
    ·
      refine ⟨33622396915384916009042149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44829862553846554678722865 33622396915384916009042149)
      ·
        refine ⟨6304199421634671751695403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33622396915384916009042149 6304199421634671751695403)
        ·
          refine ⟨9456299132452007627543105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6304199421634671751695403 9456299132452007627543105)
          ·
            refine ⟨7092224349339005720657329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9456299132452007627543105 7092224349339005720657329)
            ·
              refine ⟨5319168262004254290492997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7092224349339005720657329 5319168262004254290492997)
              ·
                refine ⟨997344049125797679467437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5319168262004254290492997 997344049125797679467437)
                ·
                  refine ⟨374004018422174129800289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 997344049125797679467437 374004018422174129800289)
                  ·
                    rfl

theorem cell21_1638833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4, 3].length) (baseStart_1638833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1638833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1638833 prefixEnd_1638833 := by exact prefixLift 1638833
  have htrace : WordTrace (prefixWord ++ tailWord_1638833) baseStart_1638833 baseEnd_1638833 := by
    simpa [prefixWord, tailWord_1638833, baseEnd_1638833] using wordTrace_append hprefix tailTrace_1638833
  have hstable : (prefixWord ++ tailWord_1638833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638833).length < 2 ^ (prefixWord ++ tailWord_1638833).sum := by decide
  have hdescent : baseEnd_1638833 < baseStart_1638833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638898 : List Nat := [3, 2, 1, 4, 3, 1, 2, 1, 4]
def baseStart_1638898 : Nat := 118140960795 + 1638898 * 2 ^ 59
def prefixEnd_1638898 : Nat := 4983230072969 + 3 ^ 40 * 1638898 * 2
def baseEnd_1638898 : Nat := 374018852307748461216823

theorem tailTrace_1638898 : CollatzResearch.WordTrace tailWord_1638898 prefixEnd_1638898 374018852307748461216823 := by
  unfold tailWord_1638898
  simp only [CollatzResearch.WordTrace]
  refine ⟨14943880204139980584853337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39850347211039948226275565 14943880204139980584853337)
  ·
    refine ⟨11207910153104985438640003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14943880204139980584853337 11207910153104985438640003)
    ·
      refine ⟨16811865229657478157960005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11207910153104985438640003 16811865229657478157960005)
      ·
        refine ⟨3152224730560777154617501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16811865229657478157960005 3152224730560777154617501)
        ·
          refine ⟨1182084273960291432981563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3152224730560777154617501 1182084273960291432981563)
          ·
            refine ⟨1773126410940437149472345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1182084273960291432981563 1773126410940437149472345)
            ·
              refine ⟨1329844808205327862104259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1773126410940437149472345 1329844808205327862104259)
              ·
                refine ⟨1994767212307991793156389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1329844808205327862104259 1994767212307991793156389)
                ·
                  refine ⟨374018852307748461216823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1994767212307991793156389 374018852307748461216823)
                  ·
                    rfl

theorem cell21_1638898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_1638898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1638898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1638898 prefixEnd_1638898 := by exact prefixLift 1638898
  have htrace : WordTrace (prefixWord ++ tailWord_1638898) baseStart_1638898 baseEnd_1638898 := by
    simpa [prefixWord, tailWord_1638898, baseEnd_1638898] using wordTrace_append hprefix tailTrace_1638898
  have hstable : (prefixWord ++ tailWord_1638898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638898).length < 2 ^ (prefixWord ++ tailWord_1638898).sum := by decide
  have hdescent : baseEnd_1638898 < baseStart_1638898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638954 : List Nat := [3, 1, 4, 1, 1, 4, 1, 6]
def baseStart_1638954 : Nat := 118140960795 + 1638954 * 2 ^ 59
def prefixEnd_1638954 : Nat := 4983230072969 + 3 ^ 40 * 1638954 * 2
def baseEnd_1638954 : Nat := 124677210756901602761125

theorem tailTrace_1638954 : CollatzResearch.WordTrace tailWord_1638954 prefixEnd_1638954 124677210756901602761125 := by
  unfold tailWord_1638954
  simp only [CollatzResearch.WordTrace]
  refine ⟨14944390826089260975862979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39851708869571362602301277 14944390826089260975862979)
  ·
    refine ⟨22416586239133891463794469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14944390826089260975862979 22416586239133891463794469)
    ·
      refine ⟨4203109919837604649461463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22416586239133891463794469 4203109919837604649461463)
      ·
        refine ⟨6304664879756406974192195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4203109919837604649461463 6304664879756406974192195)
        ·
          refine ⟨9456997319634610461288293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6304664879756406974192195 9456997319634610461288293)
          ·
            refine ⟨1773186997431489461491555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9456997319634610461288293 1773186997431489461491555)
            ·
              refine ⟨2659780496147234192237333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1773186997431489461491555 2659780496147234192237333)
              ·
                refine ⟨124677210756901602761125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2659780496147234192237333 124677210756901602761125)
                ·
                  rfl

theorem cell21_1638954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 6].length) (baseStart_1638954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1638954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1638954 prefixEnd_1638954 := by exact prefixLift 1638954
  have htrace : WordTrace (prefixWord ++ tailWord_1638954) baseStart_1638954 baseEnd_1638954 := by
    simpa [prefixWord, tailWord_1638954, baseEnd_1638954] using wordTrace_append hprefix tailTrace_1638954
  have hstable : (prefixWord ++ tailWord_1638954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638954).length < 2 ^ (prefixWord ++ tailWord_1638954).sum := by decide
  have hdescent : baseEnd_1638954 < baseStart_1638954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639030 : List Nat := [5, 1, 1, 2, 3, 1, 1, 7]
def baseStart_1639030 : Nat := 118140960795 + 1639030 * 2 ^ 59
def prefixEnd_1639030 : Nat := 4983230072969 + 3 ^ 40 * 1639030 * 2
def baseEnd_1639030 : Nat := 124682992168715188338851

theorem tailTrace_1639030 : CollatzResearch.WordTrace tailWord_1639030 prefixEnd_1639030 124682992168715188338851 := by
  unfold tailWord_1639030
  simp only [CollatzResearch.WordTrace]
  refine ⟨3736270953255106805201159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39853556834721139255479029 3736270953255106805201159)
  ·
    refine ⟨5604406429882660207801739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3736270953255106805201159 5604406429882660207801739)
    ·
      refine ⟨8406609644823990311702609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5604406429882660207801739 8406609644823990311702609)
      ·
        refine ⟨6304957233617992733776957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8406609644823990311702609 6304957233617992733776957)
        ·
          refine ⟨2364358962606747275166359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6304957233617992733776957 2364358962606747275166359)
          ·
            refine ⟨3546538443910120912749539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2364358962606747275166359 3546538443910120912749539)
            ·
              refine ⟨5319807665865181369124309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3546538443910120912749539 5319807665865181369124309)
              ·
                refine ⟨124682992168715188338851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5319807665865181369124309 124682992168715188338851)
                ·
                  rfl

theorem cell21_1639030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_1639030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1639030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1639030 prefixEnd_1639030 := by exact prefixLift 1639030
  have htrace : WordTrace (prefixWord ++ tailWord_1639030) baseStart_1639030 baseEnd_1639030 := by
    simpa [prefixWord, tailWord_1639030, baseEnd_1639030] using wordTrace_append hprefix tailTrace_1639030
  have hstable : (prefixWord ++ tailWord_1639030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639030).length < 2 ^ (prefixWord ++ tailWord_1639030).sum := by decide
  have hdescent : baseEnd_1639030 < baseStart_1639030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639230 : List Nat := [4, 2, 1, 2, 4, 1, 1, 1, 5]
def baseStart_1639230 : Nat := 118140960795 + 1639230 * 2 ^ 59
def prefixEnd_1639230 : Nat := 4983230072969 + 3 ^ 40 * 1639230 * 2
def baseEnd_1639230 : Nat := 374094619230989661682811

theorem tailTrace_1639230 : CollatzResearch.WordTrace tailWord_1639230 prefixEnd_1639230 374094619230989661682811 := by
  unfold tailWord_1639230
  simp only [CollatzResearch.WordTrace]
  refine ⟨7473453731419642880062393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39858419900904762026999429 7473453731419642880062393)
  ·
    refine ⟨5605090298564732160046795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7473453731419642880062393 5605090298564732160046795)
    ·
      refine ⟨8407635447847098240070193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5605090298564732160046795 8407635447847098240070193)
      ·
        refine ⟨6305726585885323680052645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8407635447847098240070193 6305726585885323680052645)
        ·
          refine ⟨1182323734853498190009871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6305726585885323680052645 1182323734853498190009871)
          ·
            refine ⟨1773485602280247285014807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1182323734853498190009871 1773485602280247285014807)
            ·
              refine ⟨2660228403420370927522211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1773485602280247285014807 2660228403420370927522211)
              ·
                refine ⟨3990342605130556391283317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2660228403420370927522211 3990342605130556391283317)
                ·
                  refine ⟨374094619230989661682811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3990342605130556391283317 374094619230989661682811)
                  ·
                    rfl

theorem cell21_1639230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_1639230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1639230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1639230 prefixEnd_1639230 := by exact prefixLift 1639230
  have htrace : WordTrace (prefixWord ++ tailWord_1639230) baseStart_1639230 baseEnd_1639230 := by
    simpa [prefixWord, tailWord_1639230, baseEnd_1639230] using wordTrace_append hprefix tailTrace_1639230
  have hstable : (prefixWord ++ tailWord_1639230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639230).length < 2 ^ (prefixWord ++ tailWord_1639230).sum := by decide
  have hdescent : baseEnd_1639230 < baseStart_1639230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639244 : List Nat := [2, 2, 1, 3, 3, 3, 2, 1, 4]
def baseStart_1639244 : Nat := 118140960795 + 1639244 * 2 ^ 59
def prefixEnd_1639244 : Nat := 4983230072969 + 3 ^ 40 * 1639244 * 2
def baseEnd_1639244 : Nat := 374097814221728748449449

theorem tailTrace_1639244 : CollatzResearch.WordTrace tailWord_1639244 prefixEnd_1639244 374097814221728748449449 := by
  unfold tailWord_1639244
  simp only [CollatzResearch.WordTrace]
  refine ⟨29894070236653211715754393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39858760315537615621005857 29894070236653211715754393)
  ·
    refine ⟨22420552677489908786815795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29894070236653211715754393 22420552677489908786815795)
    ·
      refine ⟨33630829016234863180223693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22420552677489908786815795 33630829016234863180223693)
      ·
        refine ⟨12611560881088073692583885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33630829016234863180223693 12611560881088073692583885)
        ·
          refine ⟨4729335330408027634718957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12611560881088073692583885 4729335330408027634718957)
          ·
            refine ⟨1773500748903010363019609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4729335330408027634718957 1773500748903010363019609)
            ·
              refine ⟨1330125561677257772264707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1773500748903010363019609 1330125561677257772264707)
              ·
                refine ⟨1995188342515886658397061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1330125561677257772264707 1995188342515886658397061)
                ·
                  refine ⟨374097814221728748449449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1995188342515886658397061 374097814221728748449449)
                  ·
                    rfl

theorem cell21_1639244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_1639244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1639244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1639244 prefixEnd_1639244 := by exact prefixLift 1639244
  have htrace : WordTrace (prefixWord ++ tailWord_1639244) baseStart_1639244 baseEnd_1639244 := by
    simpa [prefixWord, tailWord_1639244, baseEnd_1639244] using wordTrace_append hprefix tailTrace_1639244
  have hstable : (prefixWord ++ tailWord_1639244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639244).length < 2 ^ (prefixWord ++ tailWord_1639244).sum := by decide
  have hdescent : baseEnd_1639244 < baseStart_1639244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639269 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 8]
def baseStart_1639269 : Nat := 118140960795 + 1639269 * 2 ^ 59
def prefixEnd_1639269 : Nat := 4983230072969 + 3 ^ 40 * 1639269 * 2
def baseEnd_1639269 : Nat := 374103519562334260532731

theorem tailTrace_1639269 : CollatzResearch.WordTrace tailWord_1639269 prefixEnd_1639269 374103519562334260532731 := by
  unfold tailWord_1639269
  simp only [CollatzResearch.WordTrace]
  refine ⟨59789052298215852701168861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39859368198810568467445907 59789052298215852701168861)
  ·
    refine ⟨22420894611830944762938323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59789052298215852701168861 22420894611830944762938323)
    ·
      refine ⟨33631341917746417144407485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22420894611830944762938323 33631341917746417144407485)
      ·
        refine ⟨12611753219154906429152807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33631341917746417144407485 12611753219154906429152807)
        ·
          refine ⟨18917629828732359643729211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12611753219154906429152807 18917629828732359643729211)
          ·
            refine ⟨28376444743098539465593817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18917629828732359643729211 28376444743098539465593817)
            ·
              refine ⟨21282333557323904599195363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28376444743098539465593817 21282333557323904599195363)
              ·
                refine ⟨31923500335985856898793045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21282333557323904599195363 31923500335985856898793045)
                ·
                  refine ⟨374103519562334260532731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31923500335985856898793045 374103519562334260532731)
                  ·
                    rfl

theorem cell21_1639269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_1639269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1639269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1639269 prefixEnd_1639269 := by exact prefixLift 1639269
  have htrace : WordTrace (prefixWord ++ tailWord_1639269) baseStart_1639269 baseEnd_1639269 := by
    simpa [prefixWord, tailWord_1639269, baseEnd_1639269] using wordTrace_append hprefix tailTrace_1639269
  have hstable : (prefixWord ++ tailWord_1639269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639269).length < 2 ^ (prefixWord ++ tailWord_1639269).sum := by decide
  have hdescent : baseEnd_1639269 < baseStart_1639269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639289 : List Nat := [1, 2, 1, 3, 2, 3, 4, 2, 3]
def baseStart_1639289 : Nat := 118140960795 + 1639289 * 2 ^ 59
def prefixEnd_1639289 : Nat := 4983230072969 + 3 ^ 40 * 1639289 * 2
def baseEnd_1639289 : Nat := 374108083834818670199357

theorem tailTrace_1639289 : CollatzResearch.WordTrace tailWord_1639289 prefixEnd_1639289 374108083834818670199357 := by
  unfold tailWord_1639289
  simp only [CollatzResearch.WordTrace]
  refine ⟨59789781758143396116896921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39859854505428930744597947 59789781758143396116896921)
  ·
    refine ⟨44842336318607547087672691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59789781758143396116896921 44842336318607547087672691)
    ·
      refine ⟨67263504477911320631509037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44842336318607547087672691 67263504477911320631509037)
      ·
        refine ⟨25223814179216745236815889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67263504477911320631509037 25223814179216745236815889)
        ·
          refine ⟨18917860634412558927611917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25223814179216745236815889 18917860634412558927611917)
          ·
            refine ⟨7094197737904709597854469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18917860634412558927611917 7094197737904709597854469)
            ·
              refine ⟨1330162075857133049597713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7094197737904709597854469 1330162075857133049597713)
              ·
                refine ⟨997621556892849787198285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1330162075857133049597713 997621556892849787198285)
                ·
                  refine ⟨374108083834818670199357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 997621556892849787198285 374108083834818670199357)
                  ·
                    rfl

theorem cell21_1639289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 3].length) (baseStart_1639289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1639289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1639289 prefixEnd_1639289 := by exact prefixLift 1639289
  have htrace : WordTrace (prefixWord ++ tailWord_1639289) baseStart_1639289 baseEnd_1639289 := by
    simpa [prefixWord, tailWord_1639289, baseEnd_1639289] using wordTrace_append hprefix tailTrace_1639289
  have hstable : (prefixWord ++ tailWord_1639289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639289).length < 2 ^ (prefixWord ++ tailWord_1639289).sum := by decide
  have hdescent : baseEnd_1639289 < baseStart_1639289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639317 : List Nat := [1, 3, 2, 1, 1, 5, 3, 5]
def baseStart_1639317 : Nat := 118140960795 + 1639317 * 2 ^ 59
def prefixEnd_1639317 : Nat := 4983230072969 + 3 ^ 40 * 1639317 * 2
def baseEnd_1639317 : Nat := 124704824605432281244211

theorem tailTrace_1639317 : CollatzResearch.WordTrace tailWord_1639317 prefixEnd_1639317 124704824605432281244211 := by
  unfold tailWord_1639317
  simp only [CollatzResearch.WordTrace]
  refine ⟨59790803002041956898916205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39860535334694637932610803 59790803002041956898916205)
  ·
    refine ⟨22421551125765733837093577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59790803002041956898916205 22421551125765733837093577)
    ·
      refine ⟨16816163344324300377820183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22421551125765733837093577 16816163344324300377820183)
      ·
        refine ⟨25224245016486450566730275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16816163344324300377820183 25224245016486450566730275)
        ·
          refine ⟨37836367524729675850095413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25224245016486450566730275 37836367524729675850095413)
          ·
            refine ⟨3547159455443407110946445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37836367524729675850095413 3547159455443407110946445)
            ·
              refine ⟨1330184795791277666604917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3547159455443407110946445 1330184795791277666604917)
              ·
                refine ⟨124704824605432281244211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1330184795791277666604917 124704824605432281244211)
                ·
                  rfl

theorem cell21_1639317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 5].length) (baseStart_1639317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1639317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1639317 prefixEnd_1639317 := by exact prefixLift 1639317
  have htrace : WordTrace (prefixWord ++ tailWord_1639317) baseStart_1639317 baseEnd_1639317 := by
    simpa [prefixWord, tailWord_1639317, baseEnd_1639317] using wordTrace_append hprefix tailTrace_1639317
  have hstable : (prefixWord ++ tailWord_1639317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639317).length < 2 ^ (prefixWord ++ tailWord_1639317).sum := by decide
  have hdescent : baseEnd_1639317 < baseStart_1639317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639382 : List Nat := [5, 2, 1, 1, 2, 1, 3, 3, 3]
def baseStart_1639382 : Nat := 118140960795 + 1639382 * 2 ^ 59
def prefixEnd_1639382 : Nat := 4983230072969 + 3 ^ 40 * 1639382 * 2
def baseEnd_1639382 : Nat := 374129307701871175149167

theorem tailTrace_1639382 : CollatzResearch.WordTrace tailWord_1639382 prefixEnd_1639382 374129307701871175149167 := by
  unfold tailWord_1639382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3737073359175404562502025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39862115831204315333354933 3737073359175404562502025)
  ·
    refine ⟨2802805019381553421876519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3737073359175404562502025 2802805019381553421876519)
    ·
      refine ⟨4204207529072330132814779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2802805019381553421876519 4204207529072330132814779)
      ·
        refine ⟨6306311293608495199222169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4204207529072330132814779 6306311293608495199222169)
        ·
          refine ⟨4729733470206371399416627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6306311293608495199222169 4729733470206371399416627)
          ·
            refine ⟨7094600205309557099124941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4729733470206371399416627 7094600205309557099124941)
            ·
              refine ⟨2660475076991083912171853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7094600205309557099124941 2660475076991083912171853)
              ·
                refine ⟨997678153871656467064445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2660475076991083912171853 997678153871656467064445)
                ·
                  refine ⟨374129307701871175149167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 997678153871656467064445 374129307701871175149167)
                  ·
                    rfl

theorem cell21_1639382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_1639382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1639382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1639382 prefixEnd_1639382 := by exact prefixLift 1639382
  have htrace : WordTrace (prefixWord ++ tailWord_1639382) baseStart_1639382 baseEnd_1639382 := by
    simpa [prefixWord, tailWord_1639382, baseEnd_1639382] using wordTrace_append hprefix tailTrace_1639382
  have hstable : (prefixWord ++ tailWord_1639382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639382).length < 2 ^ (prefixWord ++ tailWord_1639382).sum := by decide
  have hdescent : baseEnd_1639382 < baseStart_1639382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639407 : List Nat := [1, 1, 2, 1, 4, 3, 3, 1, 5]
def baseStart_1639407 : Nat := 118140960795 + 1639407 * 2 ^ 59
def prefixEnd_1639407 : Nat := 4983230072969 + 3 ^ 40 * 1639407 * 2
def baseEnd_1639407 : Nat := 374135013042476687232449

theorem tailTrace_1639407 : CollatzResearch.WordTrace tailWord_1639407 prefixEnd_1639407 374135013042476687232449 := by
  unfold tailWord_1639407
  simp only [CollatzResearch.WordTrace]
  refine ⟨59794085571715902269692475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39862723714477268179794983 59794085571715902269692475)
  ·
    refine ⟨89691128357573853404538713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59794085571715902269692475 89691128357573853404538713)
    ·
      refine ⟨67268346268180390053404035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89691128357573853404538713 67268346268180390053404035)
      ·
        refine ⟨100902519402270585080106053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67268346268180390053404035 100902519402270585080106053)
        ·
          refine ⟨18919222387925734702519885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100902519402270585080106053 18919222387925734702519885)
          ·
            refine ⟨7094708395472150513444957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18919222387925734702519885 7094708395472150513444957)
            ·
              refine ⟨2660515648302056442541859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7094708395472150513444957 2660515648302056442541859)
              ·
                refine ⟨3990773472453084663812789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2660515648302056442541859 3990773472453084663812789)
                ·
                  refine ⟨374135013042476687232449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3990773472453084663812789 374135013042476687232449)
                  ·
                    rfl

theorem cell21_1639407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 5].length) (baseStart_1639407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1639407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1639407 prefixEnd_1639407 := by exact prefixLift 1639407
  have htrace : WordTrace (prefixWord ++ tailWord_1639407) baseStart_1639407 baseEnd_1639407 := by
    simpa [prefixWord, tailWord_1639407, baseEnd_1639407] using wordTrace_append hprefix tailTrace_1639407
  have hstable : (prefixWord ++ tailWord_1639407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639407).length < 2 ^ (prefixWord ++ tailWord_1639407).sum := by decide
  have hdescent : baseEnd_1639407 < baseStart_1639407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639410 : List Nat := [3, 2, 1, 5, 1, 1, 2, 6]
def baseStart_1639410 : Nat := 118140960795 + 1639410 * 2 ^ 59
def prefixEnd_1639410 : Nat := 4983230072969 + 3 ^ 40 * 1639410 * 2
def baseEnd_1639410 : Nat := 124711899227783116227481

theorem tailTrace_1639410 : CollatzResearch.WordTrace tailWord_1639410 prefixEnd_1639410 124711899227783116227481 := by
  unfold tailWord_1639410
  simp only [CollatzResearch.WordTrace]
  refine ⟨14948548747676258445512921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39862796660470022521367789 14948548747676258445512921)
  ·
    refine ⟨11211411560757193834134691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14948548747676258445512921 11211411560757193834134691)
    ·
      refine ⟨16817117341135790751202037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11211411560757193834134691 16817117341135790751202037)
      ·
        refine ⟨1576604750731480382925191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16817117341135790751202037 1576604750731480382925191)
        ·
          refine ⟨2364907126097220574387787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1576604750731480382925191 2364907126097220574387787)
          ·
            refine ⟨3547360689145830861581681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2364907126097220574387787 3547360689145830861581681)
            ·
              refine ⟨2660520516859373146186261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3547360689145830861581681 2660520516859373146186261)
              ·
                refine ⟨124711899227783116227481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2660520516859373146186261 124711899227783116227481)
                ·
                  rfl

theorem cell21_1639410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 6].length) (baseStart_1639410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1639410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1639410 prefixEnd_1639410 := by exact prefixLift 1639410
  have htrace : WordTrace (prefixWord ++ tailWord_1639410) baseStart_1639410 baseEnd_1639410 := by
    simpa [prefixWord, tailWord_1639410, baseEnd_1639410] using wordTrace_append hprefix tailTrace_1639410
  have hstable : (prefixWord ++ tailWord_1639410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639410).length < 2 ^ (prefixWord ++ tailWord_1639410).sum := by decide
  have hdescent : baseEnd_1639410 < baseStart_1639410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639452 : List Nat := [2, 2, 3, 1, 4, 9]
def baseStart_1639452 : Nat := 118140960795 + 1639452 * 2 ^ 59
def prefixEnd_1639452 : Nat := 4983230072969 + 3 ^ 40 * 1639452 * 2
def baseEnd_1639452 : Nat := 13857232690946911443791

theorem tailTrace_1639452 : CollatzResearch.WordTrace tailWord_1639452 prefixEnd_1639452 13857232690946911443791 := by
  unfold tailWord_1639452
  simp only [CollatzResearch.WordTrace]
  refine ⟨29897863428276437477540305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39863817904368583303387073 29897863428276437477540305)
  ·
    refine ⟨22423397571207328108155229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29897863428276437477540305 22423397571207328108155229)
    ·
      refine ⟨8408774089202748040558211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22423397571207328108155229 8408774089202748040558211)
      ·
        refine ⟨12613161133804122060837317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8408774089202748040558211 12613161133804122060837317)
        ·
          refine ⟨2364967712588272886406997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12613161133804122060837317 2364967712588272886406997)
          ·
            refine ⟨13857232690946911443791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2364967712588272886406997 13857232690946911443791)
            ·
              rfl

theorem cell21_1639452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 9].length) (baseStart_1639452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1639452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1639452 prefixEnd_1639452 := by exact prefixLift 1639452
  have htrace : WordTrace (prefixWord ++ tailWord_1639452) baseStart_1639452 baseEnd_1639452 := by
    simpa [prefixWord, tailWord_1639452, baseEnd_1639452] using wordTrace_append hprefix tailTrace_1639452
  have hstable : (prefixWord ++ tailWord_1639452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639452).length < 2 ^ (prefixWord ++ tailWord_1639452).sum := by decide
  have hdescent : baseEnd_1639452 < baseStart_1639452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639458 : List Nat := [3, 3, 1, 1, 1, 5, 2, 2, 3]
def baseStart_1639458 : Nat := 118140960795 + 1639458 * 2 ^ 59
def prefixEnd_1639458 : Nat := 4983230072969 + 3 ^ 40 * 1639458 * 2
def baseEnd_1639458 : Nat := 374146651937311931882345

theorem tailTrace_1639458 : CollatzResearch.WordTrace tailWord_1639458 prefixEnd_1639458 374146651937311931882345 := by
  unfold tailWord_1639458
  simp only [CollatzResearch.WordTrace]
  refine ⟨14948986423632784494949757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39863963796354091986532685 14948986423632784494949757)
  ·
    refine ⟨5605869908862294185606159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14948986423632784494949757 5605869908862294185606159)
    ·
      refine ⟨8408804863293441278409239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5605869908862294185606159 8408804863293441278409239)
      ·
        refine ⟨12613207294940161917613859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8408804863293441278409239 12613207294940161917613859)
        ·
          refine ⟨18919810942410242876420789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12613207294940161917613859 18919810942410242876420789)
          ·
            refine ⟨1773732275850960269664449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18919810942410242876420789 1773732275850960269664449)
            ·
              refine ⟨1330299206888220202248337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1773732275850960269664449 1330299206888220202248337)
              ·
                refine ⟨997724405166165151686253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1330299206888220202248337 997724405166165151686253)
                ·
                  refine ⟨374146651937311931882345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 997724405166165151686253 374146651937311931882345)
                  ·
                    rfl

theorem cell21_1639458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_1639458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1639458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1639458 prefixEnd_1639458 := by exact prefixLift 1639458
  have htrace : WordTrace (prefixWord ++ tailWord_1639458) baseStart_1639458 baseEnd_1639458 := by
    simpa [prefixWord, tailWord_1639458, baseEnd_1639458] using wordTrace_append hprefix tailTrace_1639458
  have hstable : (prefixWord ++ tailWord_1639458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639458).length < 2 ^ (prefixWord ++ tailWord_1639458).sum := by decide
  have hdescent : baseEnd_1639458 < baseStart_1639458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639486 : List Nat := [4, 2, 1, 3, 1, 2, 3, 5]
def baseStart_1639486 : Nat := 118140960795 + 1639486 * 2 ^ 59
def prefixEnd_1639486 : Nat := 4983230072969 + 3 ^ 40 * 1639486 * 2
def baseEnd_1639486 : Nat := 124717680639596701805207

theorem tailTrace_1639486 : CollatzResearch.WordTrace tailWord_1639486 prefixEnd_1639486 124717680639596701805207 := by
  unfold tailWord_1639486
  simp only [CollatzResearch.WordTrace]
  refine ⟨7474620867303712345227289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39864644625619799174545541 7474620867303712345227289)
  ·
    refine ⟨5605965650477784258920467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7474620867303712345227289 5605965650477784258920467)
    ·
      refine ⟨8408948475716676388380701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5605965650477784258920467 8408948475716676388380701)
      ·
        refine ⟨3153355678393753645642763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8408948475716676388380701 3153355678393753645642763)
        ·
          refine ⟨4730033517590630468464145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3153355678393753645642763 4730033517590630468464145)
          ·
            refine ⟨3547525138192972851348109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4730033517590630468464145 3547525138192972851348109)
            ·
              refine ⟨1330321926822364819255541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3547525138192972851348109 1330321926822364819255541)
              ·
                refine ⟨124717680639596701805207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1330321926822364819255541 124717680639596701805207)
                ·
                  rfl

theorem cell21_1639486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_1639486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1639486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1639486 prefixEnd_1639486 := by exact prefixLift 1639486
  have htrace : WordTrace (prefixWord ++ tailWord_1639486) baseStart_1639486 baseEnd_1639486 := by
    simpa [prefixWord, tailWord_1639486, baseEnd_1639486] using wordTrace_append hprefix tailTrace_1639486
  have hstable : (prefixWord ++ tailWord_1639486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639486).length < 2 ^ (prefixWord ++ tailWord_1639486).sum := by decide
  have hdescent : baseEnd_1639486 < baseStart_1639486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639517 : List Nat := [1, 4, 4, 1, 2, 1, 2, 1, 5]
def baseStart_1639517 : Nat := 118140960795 + 1639517 * 2 ^ 59
def prefixEnd_1639517 : Nat := 4983230072969 + 3 ^ 40 * 1639517 * 2
def baseEnd_1639517 : Nat := 374160116541140940398891

theorem tailTrace_1639517 : CollatzResearch.WordTrace tailWord_1639517 prefixEnd_1639517 374160116541140940398891 := by
  unfold tailWord_1639517
  simp only [CollatzResearch.WordTrace]
  refine ⟨59798097601317391056196805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39865398400878260704131203 59798097601317391056196805)
  ·
    refine ⟨11212143300247010823036901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59798097601317391056196805 11212143300247010823036901)
    ·
      refine ⟨2102276868796314529319419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11212143300247010823036901 2102276868796314529319419)
      ·
        refine ⟨3153415303194471793979129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2102276868796314529319419 3153415303194471793979129)
        ·
          refine ⟨2365061477395853845484347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3153415303194471793979129 2365061477395853845484347)
          ·
            refine ⟨3547592216093780768226521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2365061477395853845484347 3547592216093780768226521)
            ·
              refine ⟨2660694162070335576169891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3547592216093780768226521 2660694162070335576169891)
              ·
                refine ⟨3991041243105503364254837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2660694162070335576169891 3991041243105503364254837)
                ·
                  refine ⟨374160116541140940398891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3991041243105503364254837 374160116541140940398891)
                  ·
                    rfl

theorem cell21_1639517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_1639517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1639517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1639517 prefixEnd_1639517 := by exact prefixLift 1639517
  have htrace : WordTrace (prefixWord ++ tailWord_1639517) baseStart_1639517 baseEnd_1639517 := by
    simpa [prefixWord, tailWord_1639517, baseEnd_1639517] using wordTrace_append hprefix tailTrace_1639517
  have hstable : (prefixWord ++ tailWord_1639517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639517).length < 2 ^ (prefixWord ++ tailWord_1639517).sum := by decide
  have hdescent : baseEnd_1639517 < baseStart_1639517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639576 : List Nat := [2, 1, 2, 4, 2, 3, 1, 1, 5]
def baseStart_1639576 : Nat := 118140960795 + 1639576 * 2 ^ 59
def prefixEnd_1639576 : Nat := 4983230072969 + 3 ^ 40 * 1639576 * 2
def baseEnd_1639576 : Nat := 374173581144969948915437

theorem tailTrace_1639576 : CollatzResearch.WordTrace tailWord_1639576 prefixEnd_1639576 374173581144969948915437 := by
  unfold tailWord_1639576
  simp only [CollatzResearch.WordTrace]
  refine ⟨29900124754051822066297291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39866833005402429421729721 29900124754051822066297291)
  ·
    refine ⟨44850187131077733099445937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29900124754051822066297291 44850187131077733099445937)
    ·
      refine ⟨33637640348308299824584453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44850187131077733099445937 33637640348308299824584453)
      ·
        refine ⟨6307057565307806217109585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33637640348308299824584453 6307057565307806217109585)
        ·
          refine ⟨4730293173980854662832189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6307057565307806217109585 4730293173980854662832189)
          ·
            refine ⟨1773859940242820498562071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4730293173980854662832189 1773859940242820498562071)
            ·
              refine ⟨2660789910364230747843107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1773859940242820498562071 2660789910364230747843107)
              ·
                refine ⟨3991184865546346121764661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2660789910364230747843107 3991184865546346121764661)
                ·
                  refine ⟨374173581144969948915437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3991184865546346121764661 374173581144969948915437)
                  ·
                    rfl

theorem cell21_1639576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 5].length) (baseStart_1639576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1639576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1639576 prefixEnd_1639576 := by exact prefixLift 1639576
  have htrace : WordTrace (prefixWord ++ tailWord_1639576) baseStart_1639576 baseEnd_1639576 := by
    simpa [prefixWord, tailWord_1639576, baseEnd_1639576] using wordTrace_append hprefix tailTrace_1639576
  have hstable : (prefixWord ++ tailWord_1639576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639576).length < 2 ^ (prefixWord ++ tailWord_1639576).sum := by decide
  have hdescent : baseEnd_1639576 < baseStart_1639576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639635 : List Nat := [1, 1, 1, 2, 1, 1, 1, 10, 3]
def baseStart_1639635 : Nat := 118140960795 + 1639635 * 2 ^ 59
def prefixEnd_1639635 : Nat := 4983230072969 + 3 ^ 40 * 1639635 * 2
def baseEnd_1639635 : Nat := 374187045748798957431983

theorem tailTrace_1639635 : CollatzResearch.WordTrace tailWord_1639635 prefixEnd_1639635 374187045748798957431983 := by
  unfold tailWord_1639635
  simp only [CollatzResearch.WordTrace]
  refine ⟨59802401414889897208992359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39868267609926598139328239 59802401414889897208992359)
  ·
    refine ⟨89703602122334845813488539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59802401414889897208992359 89703602122334845813488539)
    ·
      refine ⟨134555403183502268720232809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89703602122334845813488539 134555403183502268720232809)
      ·
        refine ⟨100916552387626701540174607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134555403183502268720232809 100916552387626701540174607)
        ·
          refine ⟨151374828581440052310261911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100916552387626701540174607 151374828581440052310261911)
          ·
            refine ⟨227062242872160078465392867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151374828581440052310261911 227062242872160078465392867)
            ·
              refine ⟨340593364308240117698089301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227062242872160078465392867 340593364308240117698089301)
              ·
                refine ⟨997832121996797219818621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 340593364308240117698089301 997832121996797219818621)
                ·
                  refine ⟨374187045748798957431983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 997832121996797219818621 374187045748798957431983)
                  ·
                    rfl

theorem cell21_1639635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10, 3].length) (baseStart_1639635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1639635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1639635 prefixEnd_1639635 := by exact prefixLift 1639635
  have htrace : WordTrace (prefixWord ++ tailWord_1639635) baseStart_1639635 baseEnd_1639635 := by
    simpa [prefixWord, tailWord_1639635, baseEnd_1639635] using wordTrace_append hprefix tailTrace_1639635
  have hstable : (prefixWord ++ tailWord_1639635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639635).length < 2 ^ (prefixWord ++ tailWord_1639635).sum := by decide
  have hdescent : baseEnd_1639635 < baseStart_1639635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639714 : List Nat := [3, 3, 1, 1, 4, 2, 2, 5]
def baseStart_1639714 : Nat := 118140960795 + 1639714 * 2 ^ 59
def prefixEnd_1639714 : Nat := 4983230072969 + 3 ^ 40 * 1639714 * 2
def baseEnd_1639714 : Nat := 124735024875037458538385

theorem tailTrace_1639714 : CollatzResearch.WordTrace tailWord_1639714 prefixEnd_1639714 124735024875037458538385 := by
  unfold tailWord_1639714
  simp only [CollatzResearch.WordTrace]
  refine ⟨14951320695400923425279549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39870188521069129134078797 14951320695400923425279549)
  ·
    refine ⟨5606745260775346284479831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14951320695400923425279549 5606745260775346284479831)
    ·
      refine ⟨8410117891163019426719747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5606745260775346284479831 8410117891163019426719747)
      ·
        refine ⟨12615176836744529140079621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8410117891163019426719747 12615176836744529140079621)
        ·
          refine ⟨2365345656889599213764929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12615176836744529140079621 2365345656889599213764929)
          ·
            refine ⟨1774009242667199410323697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2365345656889599213764929 1774009242667199410323697)
            ·
              refine ⟨1330506932000399557742773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1774009242667199410323697 1330506932000399557742773)
              ·
                refine ⟨124735024875037458538385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1330506932000399557742773 124735024875037458538385)
                ·
                  rfl

theorem cell21_1639714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 5].length) (baseStart_1639714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1639714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1639714 prefixEnd_1639714 := by exact prefixLift 1639714
  have htrace : WordTrace (prefixWord ++ tailWord_1639714) baseStart_1639714 baseEnd_1639714 := by
    simpa [prefixWord, tailWord_1639714, baseEnd_1639714] using wordTrace_append hprefix tailTrace_1639714
  have hstable : (prefixWord ++ tailWord_1639714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639714).length < 2 ^ (prefixWord ++ tailWord_1639714).sum := by decide
  have hdescent : baseEnd_1639714 < baseStart_1639714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639742 : List Nat := [4, 2, 1, 2, 1, 1, 2, 4, 4]
def baseStart_1639742 : Nat := 118140960795 + 1639742 * 2 ^ 59
def prefixEnd_1639742 : Nat := 4983230072969 + 3 ^ 40 * 1639742 * 2
def baseEnd_1639742 : Nat := 374211464606590549148431

theorem tailTrace_1639742 : CollatzResearch.WordTrace tailWord_1639742 prefixEnd_1639742 374211464606590549148431 := by
  unfold tailWord_1639742
  simp only [CollatzResearch.WordTrace]
  refine ⟨7475788003187781810392185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39870869350334836322091653 7475788003187781810392185)
  ·
    refine ⟨5606841002390836357794139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7475788003187781810392185 5606841002390836357794139)
    ·
      refine ⟨8410261503586254536691209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5606841002390836357794139 8410261503586254536691209)
      ·
        refine ⟨6307696127689690902518407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8410261503586254536691209 6307696127689690902518407)
        ·
          refine ⟨9461544191534536353777611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6307696127689690902518407 9461544191534536353777611)
          ·
            refine ⟨14192316287301804530666417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9461544191534536353777611 14192316287301804530666417)
            ·
              refine ⟨10644237215476353397999813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14192316287301804530666417 10644237215476353397999813)
              ·
                refine ⟨1995794477901816262124965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10644237215476353397999813 1995794477901816262124965)
                ·
                  refine ⟨374211464606590549148431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1995794477901816262124965 374211464606590549148431)
                  ·
                    rfl

theorem cell21_1639742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_1639742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1639742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1639742 prefixEnd_1639742 := by exact prefixLift 1639742
  have htrace : WordTrace (prefixWord ++ tailWord_1639742) baseStart_1639742 baseEnd_1639742 := by
    simpa [prefixWord, tailWord_1639742, baseEnd_1639742] using wordTrace_append hprefix tailTrace_1639742
  have hstable : (prefixWord ++ tailWord_1639742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639742).length < 2 ^ (prefixWord ++ tailWord_1639742).sum := by decide
  have hdescent : baseEnd_1639742 < baseStart_1639742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639756 : List Nat := [2, 2, 1, 3, 2, 3, 2, 6]
def baseStart_1639756 : Nat := 118140960795 + 1639756 * 2 ^ 59
def prefixEnd_1639756 : Nat := 4983230072969 + 3 ^ 40 * 1639756 * 2
def baseEnd_1639756 : Nat := 124738219865776545305023

theorem tailTrace_1639756 : CollatzResearch.WordTrace tailWord_1639756 prefixEnd_1639756 124738219865776545305023 := by
  unfold tailWord_1639756
  simp only [CollatzResearch.WordTrace]
  refine ⟨29903407323725767437073561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39871209764967689916098081 29903407323725767437073561)
  ·
    refine ⟨22427555492794325577805171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29903407323725767437073561 22427555492794325577805171)
    ·
      refine ⟨33641333239191488366707757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22427555492794325577805171 33641333239191488366707757)
      ·
        refine ⟨12615499964696808137515409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33641333239191488366707757 12615499964696808137515409)
        ·
          refine ⟨9461624973522606103136557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12615499964696808137515409 9461624973522606103136557)
          ·
            refine ⟨3548109365070977288676209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9461624973522606103136557 3548109365070977288676209)
            ·
              refine ⟨2661082023803232966507157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3548109365070977288676209 2661082023803232966507157)
              ·
                refine ⟨124738219865776545305023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2661082023803232966507157 124738219865776545305023)
                ·
                  rfl

theorem cell21_1639756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 6].length) (baseStart_1639756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1639756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1639756 prefixEnd_1639756 := by exact prefixLift 1639756
  have htrace : WordTrace (prefixWord ++ tailWord_1639756) baseStart_1639756 baseEnd_1639756 := by
    simpa [prefixWord, tailWord_1639756, baseEnd_1639756] using wordTrace_append hprefix tailTrace_1639756
  have hstable : (prefixWord ++ tailWord_1639756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639756).length < 2 ^ (prefixWord ++ tailWord_1639756).sum := by decide
  have hdescent : baseEnd_1639756 < baseStart_1639756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639770 : List Nat := [3, 1, 1, 2, 1, 2, 2, 4, 5]
def baseStart_1639770 : Nat := 118140960795 + 1639770 * 2 ^ 59
def prefixEnd_1639770 : Nat := 4983230072969 + 3 ^ 40 * 1639770 * 2
def baseEnd_1639770 : Nat := 374217854588068722681707

theorem tailTrace_1639770 : CollatzResearch.WordTrace tailWord_1639770 prefixEnd_1639770 374217854588068722681707 := by
  unfold tailWord_1639770
  simp only [CollatzResearch.WordTrace]
  refine ⟨14951831317350203816289191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39871550179600543510104509 14951831317350203816289191)
  ·
    refine ⟨22427746976025305724433787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14951831317350203816289191 22427746976025305724433787)
    ·
      refine ⟨33641620464037958586650681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22427746976025305724433787 33641620464037958586650681)
      ·
        refine ⟨25231215348028468939988011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33641620464037958586650681 25231215348028468939988011)
        ·
          refine ⟨37846823022042703409982017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25231215348028468939988011 37846823022042703409982017)
          ·
            refine ⟨28385117266532027557486513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37846823022042703409982017 28385117266532027557486513)
            ·
              refine ⟨21288837949899020668114885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28385117266532027557486513 21288837949899020668114885)
              ·
                refine ⟨3991657115606066375271541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21288837949899020668114885 3991657115606066375271541)
                ·
                  refine ⟨374217854588068722681707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3991657115606066375271541 374217854588068722681707)
                  ·
                    rfl

theorem cell21_1639770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_1639770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1639770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1639770 prefixEnd_1639770 := by exact prefixLift 1639770
  have htrace : WordTrace (prefixWord ++ tailWord_1639770) baseStart_1639770 baseEnd_1639770 := by
    simpa [prefixWord, tailWord_1639770, baseEnd_1639770] using wordTrace_append hprefix tailTrace_1639770
  have hstable : (prefixWord ++ tailWord_1639770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639770).length < 2 ^ (prefixWord ++ tailWord_1639770).sum := by decide
  have hdescent : baseEnd_1639770 < baseStart_1639770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639801 : List Nat := [1, 2, 1, 3, 2, 1, 3, 4, 4]
def baseStart_1639801 : Nat := 118140960795 + 1639801 * 2 ^ 59
def prefixEnd_1639801 : Nat := 4983230072969 + 3 ^ 40 * 1639801 * 2
def baseEnd_1639801 : Nat := 374224929210419557664977

theorem tailTrace_1639801 : CollatzResearch.WordTrace tailWord_1639801 prefixEnd_1639801 374224929210419557664977 := by
  unfold tailWord_1639801
  simp only [CollatzResearch.WordTrace]
  refine ⟨59808455932288507559535257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39872303954859005039690171 59808455932288507559535257)
  ·
    refine ⟨44856341949216380669651443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59808455932288507559535257 44856341949216380669651443)
    ·
      refine ⟨67284512923824571004477165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44856341949216380669651443 67284512923824571004477165)
      ·
        refine ⟨25231692346434214126678937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67284512923824571004477165 25231692346434214126678937)
        ·
          refine ⟨18923769259825660595009203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25231692346434214126678937 18923769259825660595009203)
          ·
            refine ⟨28385653889738490892513805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18923769259825660595009203 28385653889738490892513805)
            ·
              refine ⟨10644620208651934084692677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28385653889738490892513805 10644620208651934084692677)
              ·
                refine ⟨1995866289122237640879877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10644620208651934084692677 1995866289122237640879877)
                ·
                  refine ⟨374224929210419557664977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1995866289122237640879877 374224929210419557664977)
                  ·
                    rfl

theorem cell21_1639801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 4].length) (baseStart_1639801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1639801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1639801 prefixEnd_1639801 := by exact prefixLift 1639801
  have htrace : WordTrace (prefixWord ++ tailWord_1639801) baseStart_1639801 baseEnd_1639801 := by
    simpa [prefixWord, tailWord_1639801, baseEnd_1639801] using wordTrace_append hprefix tailTrace_1639801
  have hstable : (prefixWord ++ tailWord_1639801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639801).length < 2 ^ (prefixWord ++ tailWord_1639801).sum := by decide
  have hdescent : baseEnd_1639801 < baseStart_1639801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639838 : List Nat := [4, 3, 1, 2, 2, 1, 2, 3, 3]
def baseStart_1639838 : Nat := 118140960795 + 1639838 * 2 ^ 59
def prefixEnd_1639838 : Nat := 4983230072969 + 3 ^ 40 * 1639838 * 2
def baseEnd_1639838 : Nat := 374233373114515715548235

theorem tailTrace_1639838 : CollatzResearch.WordTrace tailWord_1639838 prefixEnd_1639838 374233373114515715548235 := by
  unfold tailWord_1639838
  simp only [CollatzResearch.WordTrace]
  refine ⟨7476225679144307859829021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39873203622102975252421445 7476225679144307859829021)
  ·
    refine ⟨2803584629679115447435883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7476225679144307859829021 2803584629679115447435883)
    ·
      refine ⟨4205376944518673171153825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2803584629679115447435883 4205376944518673171153825)
      ·
        refine ⟨3154032708389004878365369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4205376944518673171153825 3154032708389004878365369)
        ·
          refine ⟨2365524531291753658774027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3154032708389004878365369 2365524531291753658774027)
          ·
            refine ⟨3548286796937630488161041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2365524531291753658774027 3548286796937630488161041)
            ·
              refine ⟨2661215097703222866120781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3548286796937630488161041 2661215097703222866120781)
              ·
                refine ⟨997955661638708574795293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2661215097703222866120781 997955661638708574795293)
                ·
                  refine ⟨374233373114515715548235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 997955661638708574795293 374233373114515715548235)
                  ·
                    rfl

theorem cell21_1639838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_1639838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1639838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1639838 prefixEnd_1639838 := by exact prefixLift 1639838
  have htrace : WordTrace (prefixWord ++ tailWord_1639838) baseStart_1639838 baseEnd_1639838 := by
    simpa [prefixWord, tailWord_1639838, baseEnd_1639838] using wordTrace_append hprefix tailTrace_1639838
  have hstable : (prefixWord ++ tailWord_1639838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639838).length < 2 ^ (prefixWord ++ tailWord_1639838).sum := by decide
  have hdescent : baseEnd_1639838 < baseStart_1639838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639863 : List Nat := [1, 1, 3, 1, 3, 2, 1, 6, 3]
def baseStart_1639863 : Nat := 118140960795 + 1639863 * 2 ^ 59
def prefixEnd_1639863 : Nat := 4983230072969 + 3 ^ 40 * 1639863 * 2
def baseEnd_1639863 : Nat := 374239078455121227631517

theorem tailTrace_1639863 : CollatzResearch.WordTrace tailWord_1639863 prefixEnd_1639863 374239078455121227631517 := by
  unfold tailWord_1639863
  simp only [CollatzResearch.WordTrace]
  refine ⟨59810717258063892148292243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39873811505375928098861495 59810717258063892148292243)
  ·
    refine ⟨89716075887095838222438365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59810717258063892148292243 89716075887095838222438365)
    ·
      refine ⟨33643528457660939333414387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89716075887095838222438365 33643528457660939333414387)
      ·
        refine ⟨50465292686491409000121581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33643528457660939333414387 50465292686491409000121581)
        ·
          refine ⟨18924484757434278375045593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50465292686491409000121581 18924484757434278375045593)
          ·
            refine ⟨14193363568075708781284195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18924484757434278375045593 14193363568075708781284195)
            ·
              refine ⟨21290045352113563171926293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14193363568075708781284195 21290045352113563171926293)
              ·
                refine ⟨997970875880323273684045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21290045352113563171926293 997970875880323273684045)
                ·
                  refine ⟨374239078455121227631517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 997970875880323273684045 374239078455121227631517)
                  ·
                    rfl

theorem cell21_1639863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6, 3].length) (baseStart_1639863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1639863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1639863 prefixEnd_1639863 := by exact prefixLift 1639863
  have htrace : WordTrace (prefixWord ++ tailWord_1639863) baseStart_1639863 baseEnd_1639863 := by
    simpa [prefixWord, tailWord_1639863, baseEnd_1639863] using wordTrace_append hprefix tailTrace_1639863
  have hstable : (prefixWord ++ tailWord_1639863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639863).length < 2 ^ (prefixWord ++ tailWord_1639863).sum := by decide
  have hdescent : baseEnd_1639863 < baseStart_1639863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639894 : List Nat := [5, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_1639894 : Nat := 118140960795 + 1639894 * 2 ^ 59
def prefixEnd_1639894 : Nat := 4983230072969 + 3 ^ 40 * 1639894 * 2
def baseEnd_1639894 : Nat := 374246153077472062614787

theorem tailTrace_1639894 : CollatzResearch.WordTrace tailWord_1639894 prefixEnd_1639894 374246153077472062614787 := by
  unfold tailWord_1639894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3738240495059474027666921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39874565280634389628447157 3738240495059474027666921)
  ·
    refine ⟨2803680371294605520750191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3738240495059474027666921 2803680371294605520750191)
    ·
      refine ⟨4205520556941908281125287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2803680371294605520750191 4205520556941908281125287)
      ·
        refine ⟨6308280835412862421687931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4205520556941908281125287 6308280835412862421687931)
        ·
          refine ⟨9462421253119293632531897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6308280835412862421687931 9462421253119293632531897)
          ·
            refine ⟨7096815939839470224398923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9462421253119293632531897 7096815939839470224398923)
            ·
              refine ⟨10645223909759205336598385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7096815939839470224398923 10645223909759205336598385)
              ·
                refine ⟨7983917932319404002448789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10645223909759205336598385 7983917932319404002448789)
                ·
                  refine ⟨374246153077472062614787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7983917932319404002448789 374246153077472062614787)
                  ·
                    rfl

theorem cell21_1639894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_1639894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1639894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1639894 prefixEnd_1639894 := by exact prefixLift 1639894
  have htrace : WordTrace (prefixWord ++ tailWord_1639894) baseStart_1639894 baseEnd_1639894 := by
    simpa [prefixWord, tailWord_1639894, baseEnd_1639894] using wordTrace_append hprefix tailTrace_1639894
  have hstable : (prefixWord ++ tailWord_1639894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639894).length < 2 ^ (prefixWord ++ tailWord_1639894).sum := by decide
  have hdescent : baseEnd_1639894 < baseStart_1639894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639925 : List Nat := [1, 3, 5, 1, 1, 2, 2, 6]
def baseStart_1639925 : Nat := 118140960795 + 1639925 * 2 ^ 59
def prefixEnd_1639925 : Nat := 4983230072969 + 3 ^ 40 * 1639925 * 2
def baseEnd_1639925 : Nat := 124751075899940965866019

theorem tailTrace_1639925 : CollatzResearch.WordTrace tailWord_1639925 prefixEnd_1639925 124751075899940965866019 := by
  unfold tailWord_1639925
  simp only [CollatzResearch.WordTrace]
  refine ⟨59812978583839276737049229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39875319055892851158032819 59812978583839276737049229)
  ·
    refine ⟨22429866968939728776393461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59812978583839276737049229 22429866968939728776393461)
    ·
      refine ⟨2102800028338099572786887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22429866968939728776393461 2102800028338099572786887)
      ·
        refine ⟨3154200042507149359180331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2102800028338099572786887 3154200042507149359180331)
        ·
          refine ⟨4731300063760724038770497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3154200042507149359180331 4731300063760724038770497)
          ·
            refine ⟨3548475047820543029077873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4731300063760724038770497 3548475047820543029077873)
            ·
              refine ⟨2661356285865407271808405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3548475047820543029077873 2661356285865407271808405)
              ·
                refine ⟨124751075899940965866019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2661356285865407271808405 124751075899940965866019)
                ·
                  rfl

theorem cell21_1639925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 6].length) (baseStart_1639925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1639925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1639925 prefixEnd_1639925 := by exact prefixLift 1639925
  have htrace : WordTrace (prefixWord ++ tailWord_1639925) baseStart_1639925 baseEnd_1639925 := by
    simpa [prefixWord, tailWord_1639925, baseEnd_1639925] using wordTrace_append hprefix tailTrace_1639925
  have hstable : (prefixWord ++ tailWord_1639925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639925).length < 2 ^ (prefixWord ++ tailWord_1639925).sum := by decide
  have hdescent : baseEnd_1639925 < baseStart_1639925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640119 : List Nat := [1, 1, 3, 1, 5, 1, 2, 7]
def baseStart_1640119 : Nat := 118140960795 + 1640119 * 2 ^ 59
def prefixEnd_1640119 : Nat := 4983230072969 + 3 ^ 40 * 1640119 * 2
def baseEnd_1640119 : Nat := 124765833714307223788109

theorem tailTrace_1640119 : CollatzResearch.WordTrace tailWord_1640119 prefixEnd_1640119 124765833714307223788109 := by
  unfold tailWord_1640119
  simp only [CollatzResearch.WordTrace]
  refine ⟨59820054345136447869611411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39880036230090965246407607 59820054345136447869611411)
  ·
    refine ⟨89730081517704671804417117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59820054345136447869611411 89730081517704671804417117)
    ·
      refine ⟨33648780569139251926656419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89730081517704671804417117 33648780569139251926656419)
      ·
        refine ⟨50473170853708877889984629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33648780569139251926656419 50473170853708877889984629)
        ·
          refine ⟨4731859767535207302186059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50473170853708877889984629 4731859767535207302186059)
          ·
            refine ⟨7097789651302810953279089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4731859767535207302186059 7097789651302810953279089)
            ·
              refine ⟨5323342238477108214959317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7097789651302810953279089 5323342238477108214959317)
              ·
                refine ⟨124765833714307223788109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5323342238477108214959317 124765833714307223788109)
                ·
                  rfl

theorem cell21_1640119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 7].length) (baseStart_1640119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1640119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1640119 prefixEnd_1640119 := by exact prefixLift 1640119
  have htrace : WordTrace (prefixWord ++ tailWord_1640119) baseStart_1640119 baseEnd_1640119 := by
    simpa [prefixWord, tailWord_1640119, baseEnd_1640119] using wordTrace_append hprefix tailTrace_1640119
  have hstable : (prefixWord ++ tailWord_1640119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640119).length < 2 ^ (prefixWord ++ tailWord_1640119).sum := by decide
  have hdescent : baseEnd_1640119 < baseStart_1640119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640133 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 7]
def baseStart_1640133 : Nat := 118140960795 + 1640133 * 2 ^ 59
def prefixEnd_1640133 : Nat := 4983230072969 + 3 ^ 40 * 1640133 * 2
def baseEnd_1640133 : Nat := 374300696133660758130965

theorem tailTrace_1640133 : CollatzResearch.WordTrace tailWord_1640133 prefixEnd_1640133 374300696133660758130965 := by
  unfold tailWord_1640133
  simp only [CollatzResearch.WordTrace]
  refine ⟨59820564967085728260621053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39880376644723818840414035 59820564967085728260621053)
  ·
    refine ⟨22432711862657148097732895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59820564967085728260621053 22432711862657148097732895)
    ·
      refine ⟨33649067793985722146599343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22432711862657148097732895 33649067793985722146599343)
      ·
        refine ⟨50473601690978583219899015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33649067793985722146599343 50473601690978583219899015)
        ·
          refine ⟨75710402536467874829848523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50473601690978583219899015 75710402536467874829848523)
          ·
            refine ⟨113565603804701812244772785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75710402536467874829848523 113565603804701812244772785)
            ·
              refine ⟨85174202853526359183579589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113565603804701812244772785 85174202853526359183579589)
              ·
                refine ⟨15970163035036192346921173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85174202853526359183579589 15970163035036192346921173)
                ·
                  refine ⟨374300696133660758130965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15970163035036192346921173 374300696133660758130965)
                  ·
                    rfl

theorem cell21_1640133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_1640133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1640133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1640133 prefixEnd_1640133 := by exact prefixLift 1640133
  have htrace : WordTrace (prefixWord ++ tailWord_1640133) baseStart_1640133 baseEnd_1640133 := by
    simpa [prefixWord, tailWord_1640133, baseEnd_1640133] using wordTrace_append hprefix tailTrace_1640133
  have hstable : (prefixWord ++ tailWord_1640133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640133).length < 2 ^ (prefixWord ++ tailWord_1640133).sum := by decide
  have hdescent : baseEnd_1640133 < baseStart_1640133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640226 : List Nat := [3, 3, 1, 1, 2, 1, 1, 4, 5]
def baseStart_1640226 : Nat := 118140960795 + 1640226 * 2 ^ 59
def prefixEnd_1640226 : Nat := 4983230072969 + 3 ^ 40 * 1640226 * 2
def baseEnd_1640226 : Nat := 374321920000713263080775

theorem tailTrace_1640226 : CollatzResearch.WordTrace tailWord_1640226 prefixEnd_1640226 374321920000713263080775 := by
  unfold tailWord_1640226
  simp only [CollatzResearch.WordTrace]
  refine ⟨14955989238937201285939133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39882637970499203429171021 14955989238937201285939133)
  ·
    refine ⟨5608495964601450482227175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14955989238937201285939133 5608495964601450482227175)
    ·
      refine ⟨8412743946902175723340763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5608495964601450482227175 8412743946902175723340763)
      ·
        refine ⟨12619115920353263585011145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8412743946902175723340763 12619115920353263585011145)
        ·
          refine ⟨9464336940264947688758359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12619115920353263585011145 9464336940264947688758359)
          ·
            refine ⟨14196505410397421533137539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9464336940264947688758359 14196505410397421533137539)
            ·
              refine ⟨21294758115596132299706309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14196505410397421533137539 21294758115596132299706309)
              ·
                refine ⟨3992767146674274806194933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21294758115596132299706309 3992767146674274806194933)
                ·
                  refine ⟨374321920000713263080775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3992767146674274806194933 374321920000713263080775)
                  ·
                    rfl

theorem cell21_1640226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_1640226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1640226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1640226 prefixEnd_1640226 := by exact prefixLift 1640226
  have htrace : WordTrace (prefixWord ++ tailWord_1640226) baseStart_1640226 baseEnd_1640226 := by
    simpa [prefixWord, tailWord_1640226, baseEnd_1640226] using wordTrace_append hprefix tailTrace_1640226
  have hstable : (prefixWord ++ tailWord_1640226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640226).length < 2 ^ (prefixWord ++ tailWord_1640226).sum := by decide
  have hdescent : baseEnd_1640226 < baseStart_1640226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640274 : List Nat := [3, 2, 2, 1, 1, 3, 4, 1, 4]
def baseStart_1640274 : Nat := 118140960795 + 1640274 * 2 ^ 59
def prefixEnd_1640274 : Nat := 4983230072969 + 3 ^ 40 * 1640274 * 2
def baseEnd_1640274 : Nat := 374332874254675846280677

theorem tailTrace_1640274 : CollatzResearch.WordTrace tailWord_1640274 prefixEnd_1640274 374332874254675846280677 := by
  unfold tailWord_1640274
  simp only [CollatzResearch.WordTrace]
  refine ⟨14956426914893727335375969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39883805106383272894335917 14956426914893727335375969)
  ·
    refine ⟨11217320186170295501531977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14956426914893727335375969 11217320186170295501531977)
    ·
      refine ⟨8412990139627721626148983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11217320186170295501531977 8412990139627721626148983)
      ·
        refine ⟨12619485209441582439223475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8412990139627721626148983 12619485209441582439223475)
        ·
          refine ⟨18929227814162373658835213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12619485209441582439223475 18929227814162373658835213)
          ·
            refine ⟨7098460430310890122063205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18929227814162373658835213 7098460430310890122063205)
            ·
              refine ⟨1330961330683291897886851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7098460430310890122063205 1330961330683291897886851)
              ·
                refine ⟨1996441996024937846830277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1330961330683291897886851 1996441996024937846830277)
                ·
                  refine ⟨374332874254675846280677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1996441996024937846830277 374332874254675846280677)
                  ·
                    rfl

theorem cell21_1640274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_1640274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1640274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1640274 prefixEnd_1640274 := by exact prefixLift 1640274
  have htrace : WordTrace (prefixWord ++ tailWord_1640274) baseStart_1640274 baseEnd_1640274 := by
    simpa [prefixWord, tailWord_1640274, baseEnd_1640274] using wordTrace_append hprefix tailTrace_1640274
  have hstable : (prefixWord ++ tailWord_1640274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640274).length < 2 ^ (prefixWord ++ tailWord_1640274).sum := by decide
  have hdescent : baseEnd_1640274 < baseStart_1640274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640429 : List Nat := [1, 5, 1, 4, 2, 1, 1, 1, 5]
def baseStart_1640429 : Nat := 118140960795 + 1640429 * 2 ^ 59
def prefixEnd_1640429 : Nat := 4983230072969 + 3 ^ 40 * 1640429 * 2
def baseEnd_1640429 : Nat := 374368247366430021197027

theorem tailTrace_1640429 : CollatzResearch.WordTrace tailWord_1640429 prefixEnd_1640429 374368247366430021197027 := by
  unfold tailWord_1640429
  simp only [CollatzResearch.WordTrace]
  refine ⟨59831360974013370813396341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39887573982675580542264227 59831360974013370813396341)
  ·
    refine ⟨5609190091313753513755907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59831360974013370813396341 5609190091313753513755907)
    ·
      refine ⟨8413785136970630270633861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5609190091313753513755907 8413785136970630270633861)
      ·
        refine ⟨1577584713181993175743849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8413785136970630270633861 1577584713181993175743849)
        ·
          refine ⟨1183188534886494881807887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1577584713181993175743849 1183188534886494881807887)
          ·
            refine ⟨1774782802329742322711831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1183188534886494881807887 1774782802329742322711831)
            ·
              refine ⟨2662174203494613484067747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1774782802329742322711831 2662174203494613484067747)
              ·
                refine ⟨3993261305241920226101621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2662174203494613484067747 3993261305241920226101621)
                ·
                  refine ⟨374368247366430021197027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3993261305241920226101621 374368247366430021197027)
                  ·
                    rfl

theorem cell21_1640429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_1640429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1640429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1640429 prefixEnd_1640429 := by exact prefixLift 1640429
  have htrace : WordTrace (prefixWord ++ tailWord_1640429) baseStart_1640429 baseEnd_1640429 := by
    simpa [prefixWord, tailWord_1640429, baseEnd_1640429] using wordTrace_append hprefix tailTrace_1640429
  have hstable : (prefixWord ++ tailWord_1640429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640429).length < 2 ^ (prefixWord ++ tailWord_1640429).sum := by decide
  have hdescent : baseEnd_1640429 < baseStart_1640429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640485 : List Nat := [1, 3, 1, 2, 2, 4, 2, 2, 4]
def baseStart_1640485 : Nat := 118140960795 + 1640485 * 2 ^ 59
def prefixEnd_1640485 : Nat := 4983230072969 + 3 ^ 40 * 1640485 * 2
def baseEnd_1640485 : Nat := 374381027329386368263579

theorem tailTrace_1640485 : CollatzResearch.WordTrace tailWord_1640485 prefixEnd_1640485 374381027329386368263579 := by
  unfold tailWord_1640485
  simp only [CollatzResearch.WordTrace]
  refine ⟨59833403461810492377434909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39888935641206994918289939 59833403461810492377434909)
  ·
    refine ⟨22437526298178934641538091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59833403461810492377434909 22437526298178934641538091)
    ·
      refine ⟨33656289447268401962307137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22437526298178934641538091 33656289447268401962307137)
      ·
        refine ⟨25242217085451301471730353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33656289447268401962307137 25242217085451301471730353)
        ·
          refine ⟨18931662814088476103797765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25242217085451301471730353 18931662814088476103797765)
          ·
            refine ⟨3549686777641589269462081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18931662814088476103797765 3549686777641589269462081)
            ·
              refine ⟨2662265083231191952096561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3549686777641589269462081 2662265083231191952096561)
              ·
                refine ⟨1996698812423393964072421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2662265083231191952096561 1996698812423393964072421)
                ·
                  refine ⟨374381027329386368263579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1996698812423393964072421 374381027329386368263579)
                  ·
                    rfl

theorem cell21_1640485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_1640485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1640485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1640485 prefixEnd_1640485 := by exact prefixLift 1640485
  have htrace : WordTrace (prefixWord ++ tailWord_1640485) baseStart_1640485 baseEnd_1640485 := by
    simpa [prefixWord, tailWord_1640485, baseEnd_1640485] using wordTrace_append hprefix tailTrace_1640485
  have hstable : (prefixWord ++ tailWord_1640485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640485).length < 2 ^ (prefixWord ++ tailWord_1640485).sum := by decide
  have hdescent : baseEnd_1640485 < baseStart_1640485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640527 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 8]
def baseStart_1640527 : Nat := 118140960795 + 1640527 * 2 ^ 59
def prefixEnd_1640527 : Nat := 4983230072969 + 3 ^ 40 * 1640527 * 2
def baseEnd_1640527 : Nat := 374390612301603628563493

theorem tailTrace_1640527 : CollatzResearch.WordTrace tailWord_1640527 prefixEnd_1640527 374390612301603628563493 := by
  unfold tailWord_1640527
  simp only [CollatzResearch.WordTrace]
  refine ⟨59834935327658333550463835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39889956885105555700309223 59834935327658333550463835)
  ·
    refine ⟨89752402991487500325695753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59834935327658333550463835 89752402991487500325695753)
    ·
      refine ⟨67314302243615625244271815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89752402991487500325695753 67314302243615625244271815)
      ·
        refine ⟨100971453365423437866407723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67314302243615625244271815 100971453365423437866407723)
        ·
          refine ⟨151457180048135156799611585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100971453365423437866407723 151457180048135156799611585)
          ·
            refine ⟨113592885036101367599708689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151457180048135156799611585 113592885036101367599708689)
            ·
              refine ⟨85194663777076025699781517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113592885036101367599708689 85194663777076025699781517)
              ·
                refine ⟨31947998916403509637418069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85194663777076025699781517 31947998916403509637418069)
                ·
                  refine ⟨374390612301603628563493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31947998916403509637418069 374390612301603628563493)
                  ·
                    rfl

theorem cell21_1640527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 8].length) (baseStart_1640527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1640527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1640527 prefixEnd_1640527 := by exact prefixLift 1640527
  have htrace : WordTrace (prefixWord ++ tailWord_1640527) baseStart_1640527 baseEnd_1640527 := by
    simpa [prefixWord, tailWord_1640527, baseEnd_1640527] using wordTrace_append hprefix tailTrace_1640527
  have hstable : (prefixWord ++ tailWord_1640527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640527).length < 2 ^ (prefixWord ++ tailWord_1640527).sum := by decide
  have hdescent : baseEnd_1640527 < baseStart_1640527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640544 : List Nat := [2, 1, 1, 3, 2, 4, 1, 1, 6]
def baseStart_1640544 : Nat := 118140960795 + 1640544 * 2 ^ 59
def prefixEnd_1640544 : Nat := 4983230072969 + 3 ^ 40 * 1640544 * 2
def baseEnd_1640544 : Nat := 374394491933215376780125

theorem tailTrace_1640544 : CollatzResearch.WordTrace tailWord_1640544 prefixEnd_1640544 374394491933215376780125 := by
  unfold tailWord_1640544
  simp only [CollatzResearch.WordTrace]
  refine ⟨29917777684298372726916343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39890370245731163635888457 29917777684298372726916343)
  ·
    refine ⟨44876666526447559090374515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29917777684298372726916343 44876666526447559090374515)
    ·
      refine ⟨67314999789671338635561773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44876666526447559090374515 67314999789671338635561773)
      ·
        refine ⟨25243124921126751988335665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67314999789671338635561773 25243124921126751988335665)
        ·
          refine ⟨18932343690845063991251749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25243124921126751988335665 18932343690845063991251749)
          ·
            refine ⟨3549814442033449498359703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18932343690845063991251749 3549814442033449498359703)
            ·
              refine ⟨5324721663050174247539555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3549814442033449498359703 5324721663050174247539555)
              ·
                refine ⟨7987082494575261371309333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5324721663050174247539555 7987082494575261371309333)
                ·
                  refine ⟨374394491933215376780125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7987082494575261371309333 374394491933215376780125)
                  ·
                    rfl

theorem cell21_1640544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 6].length) (baseStart_1640544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1640544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1640544 prefixEnd_1640544 := by exact prefixLift 1640544
  have htrace : WordTrace (prefixWord ++ tailWord_1640544) baseStart_1640544 baseEnd_1640544 := by
    simpa [prefixWord, tailWord_1640544, baseEnd_1640544] using wordTrace_append hprefix tailTrace_1640544
  have hstable : (prefixWord ++ tailWord_1640544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640544).length < 2 ^ (prefixWord ++ tailWord_1640544).sum := by decide
  have hdescent : baseEnd_1640544 < baseStart_1640544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640561 : List Nat := [1, 2, 2, 2, 1, 1, 7, 1, 4]
def baseStart_1640561 : Nat := 118140960795 + 1640561 * 2 ^ 59
def prefixEnd_1640561 : Nat := 4983230072969 + 3 ^ 40 * 1640561 * 2
def baseEnd_1640561 : Nat := 374398371564827124996757

theorem tailTrace_1640561 : CollatzResearch.WordTrace tailWord_1640561 prefixEnd_1640561 374398371564827124996757 := by
  unfold tailWord_1640561
  simp only [CollatzResearch.WordTrace]
  refine ⟨59836175409535157357201537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39890783606356771571467691 59836175409535157357201537)
  ·
    refine ⟨44877131557151368017901153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59836175409535157357201537 44877131557151368017901153)
    ·
      refine ⟨33657848667863526013425865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44877131557151368017901153 33657848667863526013425865)
      ·
        refine ⟨25243386500897644510069399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33657848667863526013425865 25243386500897644510069399)
        ·
          refine ⟨37865079751346466765104099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25243386500897644510069399 37865079751346466765104099)
          ·
            refine ⟨56797619627019700147656149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37865079751346466765104099 56797619627019700147656149)
            ·
              refine ⟨1331194210008274222210691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 56797619627019700147656149 1331194210008274222210691)
              ·
                refine ⟨1996791315012411333316037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1331194210008274222210691 1996791315012411333316037)
                ·
                  refine ⟨374398371564827124996757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1996791315012411333316037 374398371564827124996757)
                  ·
                    rfl

theorem cell21_1640561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 4].length) (baseStart_1640561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1640561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1640561 prefixEnd_1640561 := by exact prefixLift 1640561
  have htrace : WordTrace (prefixWord ++ tailWord_1640561) baseStart_1640561 baseEnd_1640561 := by
    simpa [prefixWord, tailWord_1640561, baseEnd_1640561] using wordTrace_append hprefix tailTrace_1640561
  have hstable : (prefixWord ++ tailWord_1640561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640561).length < 2 ^ (prefixWord ++ tailWord_1640561).sum := by decide
  have hdescent : baseEnd_1640561 < baseStart_1640561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640603 : List Nat := [1, 1, 1, 1, 1, 1, 2, 7, 6]
def baseStart_1640603 : Nat := 118140960795 + 1640603 * 2 ^ 59
def prefixEnd_1640603 : Nat := 4983230072969 + 3 ^ 40 * 1640603 * 2
def baseEnd_1640603 : Nat := 374407956537044385296671

theorem tailTrace_1640603 : CollatzResearch.WordTrace tailWord_1640603 prefixEnd_1640603 374407956537044385296671 := by
  unfold tailWord_1640603
  simp only [CollatzResearch.WordTrace]
  refine ⟨59837707275382998530230463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39891804850255332353486975 59837707275382998530230463)
  ·
    refine ⟨89756560913074497795345695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59837707275382998530230463 89756560913074497795345695)
    ·
      refine ⟨134634841369611746693018543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89756560913074497795345695 134634841369611746693018543)
      ·
        refine ⟨201952262054417620039527815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134634841369611746693018543 201952262054417620039527815)
        ·
          refine ⟨302928393081626430059291723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201952262054417620039527815 302928393081626430059291723)
          ·
            refine ⟨454392589622439645088937585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302928393081626430059291723 454392589622439645088937585)
            ·
              refine ⟨340794442216829733816703189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454392589622439645088937585 340794442216829733816703189)
              ·
                refine ⟨7987369739456946886328981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 340794442216829733816703189 7987369739456946886328981)
                ·
                  refine ⟨374407956537044385296671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7987369739456946886328981 374407956537044385296671)
                  ·
                    rfl

theorem cell21_1640603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 6].length) (baseStart_1640603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1640603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1640603 prefixEnd_1640603 := by exact prefixLift 1640603
  have htrace : WordTrace (prefixWord ++ tailWord_1640603) baseStart_1640603 baseEnd_1640603 := by
    simpa [prefixWord, tailWord_1640603, baseEnd_1640603] using wordTrace_append hprefix tailTrace_1640603
  have hstable : (prefixWord ++ tailWord_1640603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640603).length < 2 ^ (prefixWord ++ tailWord_1640603).sum := by decide
  have hdescent : baseEnd_1640603 < baseStart_1640603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640634 : List Nat := [3, 1, 1, 1, 2, 2, 4, 7]
def baseStart_1640634 : Nat := 118140960795 + 1640634 * 2 ^ 59
def prefixEnd_1640634 : Nat := 4983230072969 + 3 ^ 40 * 1640634 * 2
def baseEnd_1640634 : Nat := 124805010386465073426647

theorem tailTrace_1640634 : CollatzResearch.WordTrace tailWord_1640634 prefixEnd_1640634 124805010386465073426647 := by
  unfold tailWord_1640634
  simp only [CollatzResearch.WordTrace]
  refine ⟨14959709484567672706152239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39892558625513793883072637 14959709484567672706152239)
  ·
    refine ⟨22439564226851509059228359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14959709484567672706152239 22439564226851509059228359)
    ·
      refine ⟨33659346340277263588842539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22439564226851509059228359 33659346340277263588842539)
      ·
        refine ⟨50489019510415895383263809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33659346340277263588842539 50489019510415895383263809)
        ·
          refine ⟨37866764632811921537447857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50489019510415895383263809 37866764632811921537447857)
          ·
            refine ⟨28400073474608941153085893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37866764632811921537447857 28400073474608941153085893)
            ·
              refine ⟨5325013776489176466203605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28400073474608941153085893 5325013776489176466203605)
              ·
                refine ⟨124805010386465073426647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5325013776489176466203605 124805010386465073426647)
                ·
                  rfl

theorem cell21_1640634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_1640634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1640634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1640634 prefixEnd_1640634 := by exact prefixLift 1640634
  have htrace : WordTrace (prefixWord ++ tailWord_1640634) baseStart_1640634 baseEnd_1640634 := by
    simpa [prefixWord, tailWord_1640634, baseEnd_1640634] using wordTrace_append hprefix tailTrace_1640634
  have hstable : (prefixWord ++ tailWord_1640634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640634).length < 2 ^ (prefixWord ++ tailWord_1640634).sum := by decide
  have hdescent : baseEnd_1640634 < baseStart_1640634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640713 : List Nat := [1, 2, 1, 1, 3, 6, 1, 2, 4]
def baseStart_1640713 : Nat := 118140960795 + 1640713 * 2 ^ 59
def prefixEnd_1640713 : Nat := 4983230072969 + 3 ^ 40 * 1640713 * 2
def baseEnd_1640713 : Nat := 374433060035708638463113

theorem tailTrace_1640713 : CollatzResearch.WordTrace tailWord_1640713 prefixEnd_1640713 374433060035708638463113 := by
  unfold tailWord_1640713
  simp only [CollatzResearch.WordTrace]
  refine ⟨59841719304984487316734793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39894479536656324877823195 59841719304984487316734793)
  ·
    refine ⟨44881289478738365487551095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59841719304984487316734793 44881289478738365487551095)
    ·
      refine ⟨67321934218107548231326643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44881289478738365487551095 67321934218107548231326643)
      ·
        refine ⟨100982901327161322346989965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67321934218107548231326643 100982901327161322346989965)
        ·
          refine ⟨37868587997685495880121237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100982901327161322346989965 37868587997685495880121237)
          ·
            refine ⟨1775090062391507619380683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37868587997685495880121237 1775090062391507619380683)
            ·
              refine ⟨2662635093587261429071025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1775090062391507619380683 2662635093587261429071025)
              ·
                refine ⟨1996976320190446071803269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2662635093587261429071025 1996976320190446071803269)
                ·
                  refine ⟨374433060035708638463113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1996976320190446071803269 374433060035708638463113)
                  ·
                    rfl

theorem cell21_1640713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 4].length) (baseStart_1640713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1640713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1640713 prefixEnd_1640713 := by exact prefixLift 1640713
  have htrace : WordTrace (prefixWord ++ tailWord_1640713) baseStart_1640713 baseEnd_1640713 := by
    simpa [prefixWord, tailWord_1640713, baseEnd_1640713] using wordTrace_append hprefix tailTrace_1640713
  have hstable : (prefixWord ++ tailWord_1640713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640713).length < 2 ^ (prefixWord ++ tailWord_1640713).sum := by decide
  have hdescent : baseEnd_1640713 < baseStart_1640713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640730 : List Nat := [3, 1, 1, 3, 4, 1, 3, 1, 4]
def baseStart_1640730 : Nat := 118140960795 + 1640730 * 2 ^ 59
def prefixEnd_1640730 : Nat := 4983230072969 + 3 ^ 40 * 1640730 * 2
def baseEnd_1640730 : Nat := 374436939667320386679745

theorem tailTrace_1640730 : CollatzResearch.WordTrace tailWord_1640730 prefixEnd_1640730 374436939667320386679745 := by
  unfold tailWord_1640730
  simp only [CollatzResearch.WordTrace]
  refine ⟨14960584836480724805025911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39894892897281932813402429 14960584836480724805025911)
  ·
    refine ⟨22440877254721087207538867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14960584836480724805025911 22440877254721087207538867)
    ·
      refine ⟨33661315882081630811308301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22440877254721087207538867 33661315882081630811308301)
      ·
        refine ⟨12622993455780611554240613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33661315882081630811308301 12622993455780611554240613)
        ·
          refine ⟨2366811272958864666420115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12622993455780611554240613 2366811272958864666420115)
          ·
            refine ⟨3550216909438296999630173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2366811272958864666420115 3550216909438296999630173)
            ·
              refine ⟨1331331341039361374861315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3550216909438296999630173 1331331341039361374861315)
              ·
                refine ⟨1996997011559042062291973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1331331341039361374861315 1996997011559042062291973)
                ·
                  refine ⟨374436939667320386679745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1996997011559042062291973 374436939667320386679745)
                  ·
                    rfl

theorem cell21_1640730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_1640730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1640730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1640730 prefixEnd_1640730 := by exact prefixLift 1640730
  have htrace : WordTrace (prefixWord ++ tailWord_1640730) baseStart_1640730 baseEnd_1640730 := by
    simpa [prefixWord, tailWord_1640730, baseEnd_1640730] using wordTrace_append hprefix tailTrace_1640730
  have hstable : (prefixWord ++ tailWord_1640730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640730).length < 2 ^ (prefixWord ++ tailWord_1640730).sum := by decide
  have hdescent : baseEnd_1640730 < baseStart_1640730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640750 : List Nat := [4, 1, 3, 3, 2, 1, 1, 3, 3]
def baseStart_1640750 : Nat := 118140960795 + 1640750 * 2 ^ 59
def prefixEnd_1640750 : Nat := 4983230072969 + 3 ^ 40 * 1640750 * 2
def baseEnd_1640750 : Nat := 374441503939804796346371

theorem tailTrace_1640750 : CollatzResearch.WordTrace tailWord_1640750 prefixEnd_1640750 374441503939804796346371 := by
  unfold tailWord_1640750
  simp only [CollatzResearch.WordTrace]
  refine ⟨7480383600731305329478963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39895379203900295090554469 7480383600731305329478963)
  ·
    refine ⟨11220575401096957994218445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7480383600731305329478963 11220575401096957994218445)
    ·
      refine ⟨4207715775411359247831917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11220575401096957994218445 4207715775411359247831917)
      ·
        refine ⟨1577893415779259717936969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4207715775411359247831917 1577893415779259717936969)
        ·
          refine ⟨1183420061834444788452727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1577893415779259717936969 1183420061834444788452727)
          ·
            refine ⟨1775130092751667182679091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1183420061834444788452727 1775130092751667182679091)
            ·
              refine ⟨2662695139127500774018637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1775130092751667182679091 2662695139127500774018637)
              ·
                refine ⟨998510677172812790256989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2662695139127500774018637 998510677172812790256989)
                ·
                  refine ⟨374441503939804796346371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 998510677172812790256989 374441503939804796346371)
                  ·
                    rfl

theorem cell21_1640750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_1640750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1640750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1640750 prefixEnd_1640750 := by exact prefixLift 1640750
  have htrace : WordTrace (prefixWord ++ tailWord_1640750) baseStart_1640750 baseEnd_1640750 := by
    simpa [prefixWord, tailWord_1640750, baseEnd_1640750] using wordTrace_append hprefix tailTrace_1640750
  have hstable : (prefixWord ++ tailWord_1640750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640750).length < 2 ^ (prefixWord ++ tailWord_1640750).sum := by decide
  have hdescent : baseEnd_1640750 < baseStart_1640750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640755 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 8]
def baseStart_1640755 : Nat := 118140960795 + 1640755 * 2 ^ 59
def prefixEnd_1640755 : Nat := 4983230072969 + 3 ^ 40 * 1640755 * 2
def baseEnd_1640755 : Nat := 374442645007925898763027

theorem tailTrace_1640755 : CollatzResearch.WordTrace tailWord_1640755 prefixEnd_1640755 374442645007925898763027 := by
  unfold tailWord_1640755
  simp only [CollatzResearch.WordTrace]
  refine ⟨59843251170832328489763719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39895500780554885659842479 59843251170832328489763719)
  ·
    refine ⟨89764876756248492734645579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59843251170832328489763719 89764876756248492734645579)
    ·
      refine ⟨134647315134372739101968369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89764876756248492734645579 134647315134372739101968369)
      ·
        refine ⟨100985486350779554326476277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134647315134372739101968369 100985486350779554326476277)
        ·
          refine ⟨9467389345385583218107151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100985486350779554326476277 9467389345385583218107151)
          ·
            refine ⟨14201084018078374827160727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9467389345385583218107151 14201084018078374827160727)
            ·
              refine ⟨21301626027117562240741091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14201084018078374827160727 21301626027117562240741091)
              ·
                refine ⟨31952439040676343361111637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21301626027117562240741091 31952439040676343361111637)
                ·
                  refine ⟨374442645007925898763027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31952439040676343361111637 374442645007925898763027)
                  ·
                    rfl

theorem cell21_1640755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 8].length) (baseStart_1640755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1640755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1640755 prefixEnd_1640755 := by exact prefixLift 1640755
  have htrace : WordTrace (prefixWord ++ tailWord_1640755) baseStart_1640755 baseEnd_1640755 := by
    simpa [prefixWord, tailWord_1640755, baseEnd_1640755] using wordTrace_append hprefix tailTrace_1640755
  have hstable : (prefixWord ++ tailWord_1640755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640755).length < 2 ^ (prefixWord ++ tailWord_1640755).sum := by decide
  have hdescent : baseEnd_1640755 < baseStart_1640755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640775 : List Nat := [1, 1, 4, 1, 2, 2, 5, 2, 3]
def baseStart_1640775 : Nat := 118140960795 + 1640775 * 2 ^ 59
def prefixEnd_1640775 : Nat := 4983230072969 + 3 ^ 40 * 1640775 * 2
def baseEnd_1640775 : Nat := 374447209280410308429653

theorem tailTrace_1640775 : CollatzResearch.WordTrace tailWord_1640775 prefixEnd_1640775 374447209280410308429653 := by
  unfold tailWord_1640775
  simp only [CollatzResearch.WordTrace]
  refine ⟨59843980630759871905491779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39895987087173247936994519 59843980630759871905491779)
  ·
    refine ⟨89765970946139807858237669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59843980630759871905491779 89765970946139807858237669)
    ·
      refine ⟨16831119552401213973419563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89765970946139807858237669 16831119552401213973419563)
      ·
        refine ⟨25246679328601820960129345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16831119552401213973419563 25246679328601820960129345)
        ·
          refine ⟨18935009496451365720097009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25246679328601820960129345 18935009496451365720097009)
          ·
            refine ⟨14201257122338524290072757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18935009496451365720097009 14201257122338524290072757)
            ·
              refine ⟨1331367855219236652194321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14201257122338524290072757 1331367855219236652194321)
              ·
                refine ⟨998525891414427489145741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1331367855219236652194321 998525891414427489145741)
                ·
                  refine ⟨374447209280410308429653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 998525891414427489145741 374447209280410308429653)
                  ·
                    rfl

theorem cell21_1640775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2, 3].length) (baseStart_1640775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1640775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1640775 prefixEnd_1640775 := by exact prefixLift 1640775
  have htrace : WordTrace (prefixWord ++ tailWord_1640775) baseStart_1640775 baseEnd_1640775 := by
    simpa [prefixWord, tailWord_1640775, baseEnd_1640775] using wordTrace_append hprefix tailTrace_1640775
  have hstable : (prefixWord ++ tailWord_1640775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640775).length < 2 ^ (prefixWord ++ tailWord_1640775).sum := by decide
  have hdescent : baseEnd_1640775 < baseStart_1640775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640786 : List Nat := [3, 2, 2, 1, 1, 1, 3, 8]
def baseStart_1640786 : Nat := 118140960795 + 1640786 * 2 ^ 59
def prefixEnd_1640786 : Nat := 4983230072969 + 3 ^ 40 * 1640786 * 2
def baseEnd_1640786 : Nat := 124816573210092244582099

theorem tailTrace_1640786 : CollatzResearch.WordTrace tailWord_1640786 prefixEnd_1640786 124816573210092244582099 := by
  unfold tailWord_1640786
  simp only [CollatzResearch.WordTrace]
  refine ⟨14961095458430005196035553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39896254555813347189428141 14961095458430005196035553)
  ·
    refine ⟨11220821593822503897026665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14961095458430005196035553 11220821593822503897026665)
    ·
      refine ⟨8415616195366877922769999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11220821593822503897026665 8415616195366877922769999)
      ·
        refine ⟨12623424293050316884154999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8415616195366877922769999 12623424293050316884154999)
        ·
          refine ⟨18935136439575475326232499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12623424293050316884154999 18935136439575475326232499)
          ·
            refine ⟨28402704659363212989348749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18935136439575475326232499 28402704659363212989348749)
            ·
              refine ⟨10651014247261204871005781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28402704659363212989348749 10651014247261204871005781)
              ·
                refine ⟨124816573210092244582099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10651014247261204871005781 124816573210092244582099)
                ·
                  rfl

theorem cell21_1640786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_1640786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1640786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1640786 prefixEnd_1640786 := by exact prefixLift 1640786
  have htrace : WordTrace (prefixWord ++ tailWord_1640786) baseStart_1640786 baseEnd_1640786 := by
    simpa [prefixWord, tailWord_1640786, baseEnd_1640786] using wordTrace_append hprefix tailTrace_1640786
  have hstable : (prefixWord ++ tailWord_1640786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640786).length < 2 ^ (prefixWord ++ tailWord_1640786).sum := by decide
  have hdescent : baseEnd_1640786 < baseStart_1640786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640789 : List Nat := [1, 3, 2, 2, 4, 1, 1, 3, 4]
def baseStart_1640789 : Nat := 118140960795 + 1640789 * 2 ^ 59
def prefixEnd_1640789 : Nat := 4983230072969 + 3 ^ 40 * 1640789 * 2
def baseEnd_1640789 : Nat := 374450404271149395196291

theorem tailTrace_1640789 : CollatzResearch.WordTrace tailWord_1640789 prefixEnd_1640789 374450404271149395196291 := by
  unfold tailWord_1640789
  simp only [CollatzResearch.WordTrace]
  refine ⟨59844491252709152296501421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39896327501806101531000947 59844491252709152296501421)
  ·
    refine ⟨22441684219765932111188033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59844491252709152296501421 22441684219765932111188033)
    ·
      refine ⟨16831263164824449083391025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22441684219765932111188033 16831263164824449083391025)
      ·
        refine ⟨12623447373618336812543269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16831263164824449083391025 12623447373618336812543269)
        ·
          refine ⟨2366896382553438152351863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12623447373618336812543269 2366896382553438152351863)
          ·
            refine ⟨3550344573830157228527795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2366896382553438152351863 3550344573830157228527795)
            ·
              refine ⟨5325516860745235842791693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3550344573830157228527795 5325516860745235842791693)
              ·
                refine ⟨1997068822779463441046885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5325516860745235842791693 1997068822779463441046885)
                ·
                  refine ⟨374450404271149395196291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1997068822779463441046885 374450404271149395196291)
                  ·
                    rfl

theorem cell21_1640789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_1640789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1640789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1640789 prefixEnd_1640789 := by exact prefixLift 1640789
  have htrace : WordTrace (prefixWord ++ tailWord_1640789) baseStart_1640789 baseEnd_1640789 := by
    simpa [prefixWord, tailWord_1640789, baseEnd_1640789] using wordTrace_append hprefix tailTrace_1640789
  have hstable : (prefixWord ++ tailWord_1640789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640789).length < 2 ^ (prefixWord ++ tailWord_1640789).sum := by decide
  have hdescent : baseEnd_1640789 < baseStart_1640789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640876 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 9]
def baseStart_1640876 : Nat := 118140960795 + 1640876 * 2 ^ 59
def prefixEnd_1640876 : Nat := 4983230072969 + 3 ^ 40 * 1640876 * 2
def baseEnd_1640876 : Nat := 374470258856456577246113

theorem tailTrace_1640876 : CollatzResearch.WordTrace tailWord_1640876 prefixEnd_1640876 374470258856456577246113 := by
  unfold tailWord_1640876
  simp only [CollatzResearch.WordTrace]
  refine ⟨29923832201696983077459241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39898442935595977436612321 29923832201696983077459241)
  ·
    refine ⟨22442874151272737308094431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29923832201696983077459241 22442874151272737308094431)
    ·
      refine ⟨33664311226909105962141647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22442874151272737308094431 33664311226909105962141647)
      ·
        refine ⟨50496466840363658943212471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33664311226909105962141647 50496466840363658943212471)
        ·
          refine ⟨75744700260545488414818707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50496466840363658943212471 75744700260545488414818707)
          ·
            refine ⟨113617050390818232622228061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75744700260545488414818707 113617050390818232622228061)
            ·
              refine ⟨42606393896556837233335523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113617050390818232622228061 42606393896556837233335523)
              ·
                refine ⟨63909590844835255850003285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42606393896556837233335523 63909590844835255850003285)
                ·
                  refine ⟨374470258856456577246113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63909590844835255850003285 374470258856456577246113)
                  ·
                    rfl

theorem cell21_1640876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_1640876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1640876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1640876 prefixEnd_1640876 := by exact prefixLift 1640876
  have htrace : WordTrace (prefixWord ++ tailWord_1640876) baseStart_1640876 baseEnd_1640876 := by
    simpa [prefixWord, tailWord_1640876, baseEnd_1640876] using wordTrace_append hprefix tailTrace_1640876
  have hstable : (prefixWord ++ tailWord_1640876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640876).length < 2 ^ (prefixWord ++ tailWord_1640876).sum := by decide
  have hdescent : baseEnd_1640876 < baseStart_1640876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640893 : List Nat := [1, 4, 1, 2, 2, 2, 1, 3, 5]
def baseStart_1640893 : Nat := 118140960795 + 1640893 * 2 ^ 59
def prefixEnd_1640893 : Nat := 4983230072969 + 3 ^ 40 * 1640893 * 2
def baseEnd_1640893 : Nat := 374474138488068325462745

theorem tailTrace_1640893 : CollatzResearch.WordTrace tailWord_1640893 prefixEnd_1640893 374474138488068325462745 := by
  unfold tailWord_1640893
  simp only [CollatzResearch.WordTrace]
  refine ⟨59848284444332378058287333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39898856296221585372191555 59848284444332378058287333)
  ·
    refine ⟨11221553333312320885928875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59848284444332378058287333 11221553333312320885928875)
    ·
      refine ⟨16832329999968481328893313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11221553333312320885928875 16832329999968481328893313)
      ·
        refine ⟨12624247499976360996669985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16832329999968481328893313 12624247499976360996669985)
        ·
          refine ⟨9468185624982270747502489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12624247499976360996669985 9468185624982270747502489)
          ·
            refine ⟨7101139218736703060626867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9468185624982270747502489 7101139218736703060626867)
            ·
              refine ⟨10651708828105054590940301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7101139218736703060626867 10651708828105054590940301)
              ·
                refine ⟨3994390810539395471602613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10651708828105054590940301 3994390810539395471602613)
                ·
                  refine ⟨374474138488068325462745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3994390810539395471602613 374474138488068325462745)
                  ·
                    rfl

theorem cell21_1640893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_1640893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1640893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1640893 prefixEnd_1640893 := by exact prefixLift 1640893
  have htrace : WordTrace (prefixWord ++ tailWord_1640893) baseStart_1640893 baseEnd_1640893 := by
    simpa [prefixWord, tailWord_1640893, baseEnd_1640893] using wordTrace_append hprefix tailTrace_1640893
  have hstable : (prefixWord ++ tailWord_1640893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640893).length < 2 ^ (prefixWord ++ tailWord_1640893).sum := by decide
  have hdescent : baseEnd_1640893 < baseStart_1640893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640927 : List Nat := [1, 1, 2, 3, 3, 4, 1, 3, 3]
def baseStart_1640927 : Nat := 118140960795 + 1640927 * 2 ^ 59
def prefixEnd_1640927 : Nat := 4983230072969 + 3 ^ 40 * 1640927 * 2
def baseEnd_1640927 : Nat := 374481897751291821896009

theorem tailTrace_1640927 : CollatzResearch.WordTrace tailWord_1640927 prefixEnd_1640927 374481897751291821896009 := by
  unfold tailWord_1640927
  simp only [CollatzResearch.WordTrace]
  refine ⟨59849524526209201865025035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39899683017472801243350023 59849524526209201865025035)
  ·
    refine ⟨89774286789313802797537553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59849524526209201865025035 89774286789313802797537553)
    ·
      refine ⟨67330715091985352098153165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89774286789313802797537553 67330715091985352098153165)
      ·
        refine ⟨25249018159494507036807437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67330715091985352098153165 25249018159494507036807437)
        ·
          refine ⟨9468381809810440138802789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25249018159494507036807437 9468381809810440138802789)
          ·
            refine ⟨1775321589339457526025523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9468381809810440138802789 1775321589339457526025523)
            ·
              refine ⟨2662982384009186289038285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1775321589339457526025523 2662982384009186289038285)
              ·
                refine ⟨998618394003444858389357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2662982384009186289038285 998618394003444858389357)
                ·
                  refine ⟨374481897751291821896009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 998618394003444858389357 374481897751291821896009)
                  ·
                    rfl

theorem cell21_1640927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3, 3].length) (baseStart_1640927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1640927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1640927 prefixEnd_1640927 := by exact prefixLift 1640927
  have htrace : WordTrace (prefixWord ++ tailWord_1640927) baseStart_1640927 baseEnd_1640927 := by
    simpa [prefixWord, tailWord_1640927, baseEnd_1640927] using wordTrace_append hprefix tailTrace_1640927
  have hstable : (prefixWord ++ tailWord_1640927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640927).length < 2 ^ (prefixWord ++ tailWord_1640927).sum := by decide
  have hdescent : baseEnd_1640927 < baseStart_1640927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640938 : List Nat := [3, 1, 3, 1, 3, 1, 9]
def baseStart_1640938 : Nat := 118140960795 + 1640938 * 2 ^ 59
def prefixEnd_1640938 : Nat := 4983230072969 + 3 ^ 40 * 1640938 * 2
def baseEnd_1640938 : Nat := 41609378677906471912517

theorem tailTrace_1640938 : CollatzResearch.WordTrace tailWord_1640938 prefixEnd_1640938 41609378677906471912517 := by
  unfold tailWord_1640938
  simp only [CollatzResearch.WordTrace]
  refine ⟨14962481432292337685918867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39899950486112900495783645 14962481432292337685918867)
  ·
    refine ⟨22443722148438506528878301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14962481432292337685918867 22443722148438506528878301)
    ·
      refine ⟨8416395805664439948329363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22443722148438506528878301 8416395805664439948329363)
      ·
        refine ⟨12624593708496659922494045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8416395805664439948329363 12624593708496659922494045)
        ·
          refine ⟨4734222640686247470935267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12624593708496659922494045 4734222640686247470935267)
          ·
            refine ⟨7101333961029371206402901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4734222640686247470935267 7101333961029371206402901)
            ·
              refine ⟨41609378677906471912517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7101333961029371206402901 41609378677906471912517)
              ·
                rfl

theorem cell21_1640938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 9].length) (baseStart_1640938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1640938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1640938 prefixEnd_1640938 := by exact prefixLift 1640938
  have htrace : WordTrace (prefixWord ++ tailWord_1640938) baseStart_1640938 baseEnd_1640938 := by
    simpa [prefixWord, tailWord_1640938, baseEnd_1640938] using wordTrace_append hprefix tailTrace_1640938
  have hstable : (prefixWord ++ tailWord_1640938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640938).length < 2 ^ (prefixWord ++ tailWord_1640938).sum := by decide
  have hdescent : baseEnd_1640938 < baseStart_1640938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641031 : List Nat := [1, 1, 4, 1, 4, 2, 3, 5]
def baseStart_1641031 : Nat := 118140960795 + 1641031 * 2 ^ 59
def prefixEnd_1641031 : Nat := 4983230072969 + 3 ^ 40 * 1641031 * 2
def baseEnd_1641031 : Nat := 124835210656070250720821

theorem tailTrace_1641031 : CollatzResearch.WordTrace tailWord_1641031 prefixEnd_1641031 124835210656070250720821 := by
  unfold tailWord_1641031
  simp only [CollatzResearch.WordTrace]
  refine ⟨59853317717832427626810947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39902211811888285084540631 59853317717832427626810947)
  ·
    refine ⟨89779976576748641440216421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59853317717832427626810947 89779976576748641440216421)
    ·
      refine ⟨16833745608140370270040579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89779976576748641440216421 16833745608140370270040579)
      ·
        refine ⟨25250618412210555405060869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16833745608140370270040579 25250618412210555405060869)
        ·
          refine ⟨4734490952289479138448913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25250618412210555405060869 4734490952289479138448913)
          ·
            refine ⟨3550868214217109353836685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4734490952289479138448913 3550868214217109353836685)
            ·
              refine ⟨1331575580331416007688757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3550868214217109353836685 1331575580331416007688757)
              ·
                refine ⟨124835210656070250720821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1331575580331416007688757 124835210656070250720821)
                ·
                  rfl

theorem cell21_1641031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 5].length) (baseStart_1641031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1641031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1641031 prefixEnd_1641031 := by exact prefixLift 1641031
  have htrace : WordTrace (prefixWord ++ tailWord_1641031) baseStart_1641031 baseEnd_1641031 := by
    simpa [prefixWord, tailWord_1641031, baseEnd_1641031] using wordTrace_append hprefix tailTrace_1641031
  have hstable : (prefixWord ++ tailWord_1641031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641031).length < 2 ^ (prefixWord ++ tailWord_1641031).sum := by decide
  have hdescent : baseEnd_1641031 < baseStart_1641031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641059 : List Nat := [1, 1, 1, 5, 1, 2, 3, 1, 6]
def baseStart_1641059 : Nat := 118140960795 + 1641059 * 2 ^ 59
def prefixEnd_1641059 : Nat := 4983230072969 + 3 ^ 40 * 1641059 * 2
def baseEnd_1641059 : Nat := 374512021949688925695739

theorem tailTrace_1641059 : CollatzResearch.WordTrace tailWord_1641059 prefixEnd_1641059 374512021949688925695739 := by
  unfold tailWord_1641059
  simp only [CollatzResearch.WordTrace]
  refine ⟨59854338961730988408830231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39902892641153992272553487 59854338961730988408830231)
  ·
    refine ⟨89781508442596482613245347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59854338961730988408830231 89781508442596482613245347)
    ·
      refine ⟨134672262663894723919868021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89781508442596482613245347 134672262663894723919868021)
      ·
        refine ⟨12625524624740130367487627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134672262663894723919868021 12625524624740130367487627)
        ·
          refine ⟨18938286937110195551231441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12625524624740130367487627 18938286937110195551231441)
          ·
            refine ⟨14203715202832646663423581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18938286937110195551231441 14203715202832646663423581)
            ·
              refine ⟨5326393201062242498783843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14203715202832646663423581 5326393201062242498783843)
              ·
                refine ⟨7989589801593363748175765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5326393201062242498783843 7989589801593363748175765)
                ·
                  refine ⟨374512021949688925695739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7989589801593363748175765 374512021949688925695739)
                  ·
                    rfl

theorem cell21_1641059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 6].length) (baseStart_1641059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1641059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1641059 prefixEnd_1641059 := by exact prefixLift 1641059
  have htrace : WordTrace (prefixWord ++ tailWord_1641059) baseStart_1641059 baseEnd_1641059 := by
    simpa [prefixWord, tailWord_1641059, baseEnd_1641059] using wordTrace_append hprefix tailTrace_1641059
  have hstable : (prefixWord ++ tailWord_1641059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641059).length < 2 ^ (prefixWord ++ tailWord_1641059).sum := by decide
  have hdescent : baseEnd_1641059 < baseStart_1641059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641127 : List Nat := [1, 1, 6, 3, 1, 2, 2, 1, 4]
def baseStart_1641127 : Nat := 118140960795 + 1641127 * 2 ^ 59
def prefixEnd_1641127 : Nat := 4983230072969 + 3 ^ 40 * 1641127 * 2
def baseEnd_1641127 : Nat := 374527540476135918562267

theorem tailTrace_1641127 : CollatzResearch.WordTrace tailWord_1641127 prefixEnd_1641127 374527540476135918562267 := by
  unfold tailWord_1641127
  simp only [CollatzResearch.WordTrace]
  refine ⟨59856819125484636022305635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39904546083656424014870423 59856819125484636022305635)
  ·
    refine ⟨89785228688226954033458453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59856819125484636022305635 89785228688226954033458453)
    ·
      refine ⟨4208682594760638470318365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89785228688226954033458453 4208682594760638470318365)
      ·
        refine ⟨1578255973035239426369387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4208682594760638470318365 1578255973035239426369387)
        ·
          refine ⟨2367383959552859139554081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1578255973035239426369387 2367383959552859139554081)
          ·
            refine ⟨1775537969664644354665561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2367383959552859139554081 1775537969664644354665561)
            ·
              refine ⟨1331653477248483265999171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1775537969664644354665561 1331653477248483265999171)
              ·
                refine ⟨1997480215872724898998757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1331653477248483265999171 1997480215872724898998757)
                ·
                  refine ⟨374527540476135918562267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1997480215872724898998757 374527540476135918562267)
                  ·
                    rfl

theorem cell21_1641127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 4].length) (baseStart_1641127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1641127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1641127 prefixEnd_1641127 := by exact prefixLift 1641127
  have htrace : WordTrace (prefixWord ++ tailWord_1641127) baseStart_1641127 baseEnd_1641127 := by
    simpa [prefixWord, tailWord_1641127, baseEnd_1641127] using wordTrace_append hprefix tailTrace_1641127
  have hstable : (prefixWord ++ tailWord_1641127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641127).length < 2 ^ (prefixWord ++ tailWord_1641127).sum := by decide
  have hdescent : baseEnd_1641127 < baseStart_1641127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641197 : List Nat := [1, 5, 1, 2, 1, 1, 3, 2, 5]
def baseStart_1641197 : Nat := 118140960795 + 1641197 * 2 ^ 59
def prefixEnd_1641197 : Nat := 4983230072969 + 3 ^ 40 * 1641197 * 2
def baseEnd_1641197 : Nat := 374543515429831352395457

theorem tailTrace_1641197 : CollatzResearch.WordTrace tailWord_1641197 prefixEnd_1641197 374543515429831352395457 := by
  unfold tailWord_1641197
  simp only [CollatzResearch.WordTrace]
  refine ⟨59859372235231037977353845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39906248156820691984902563 59859372235231037977353845)
  ·
    refine ⟨5611816147052909810376923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59859372235231037977353845 5611816147052909810376923)
    ·
      refine ⟨8417724220579364715565385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5611816147052909810376923 8417724220579364715565385)
      ·
        refine ⟨6313293165434523536674039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8417724220579364715565385 6313293165434523536674039)
        ·
          refine ⟨9469939748151785305011059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6313293165434523536674039 9469939748151785305011059)
          ·
            refine ⟨14204909622227677957516589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9469939748151785305011059 14204909622227677957516589)
            ·
              refine ⟨5326841108335379234068721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14204909622227677957516589 5326841108335379234068721)
              ·
                refine ⟨3995130831251534425551541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5326841108335379234068721 3995130831251534425551541)
                ·
                  refine ⟨374543515429831352395457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3995130831251534425551541 374543515429831352395457)
                  ·
                    rfl

theorem cell21_1641197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_1641197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1641197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1641197 prefixEnd_1641197 := by exact prefixLift 1641197
  have htrace : WordTrace (prefixWord ++ tailWord_1641197) baseStart_1641197 baseEnd_1641197 := by
    simpa [prefixWord, tailWord_1641197, baseEnd_1641197] using wordTrace_append hprefix tailTrace_1641197
  have hstable : (prefixWord ++ tailWord_1641197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641197).length < 2 ^ (prefixWord ++ tailWord_1641197).sum := by decide
  have hdescent : baseEnd_1641197 < baseStart_1641197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641287 : List Nat := [1, 1, 4, 1, 2, 1, 1, 6, 4]
def baseStart_1641287 : Nat := 118140960795 + 1641287 * 2 ^ 59
def prefixEnd_1641287 : Nat := 4983230072969 + 3 ^ 40 * 1641287 * 2
def baseEnd_1641287 : Nat := 374564054656011195895273

theorem tailTrace_1641287 : CollatzResearch.WordTrace tailWord_1641287 prefixEnd_1641287 374564054656011195895273 := by
  unfold tailWord_1641287
  simp only [CollatzResearch.WordTrace]
  refine ⟨59862654804904983348130115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39908436536603322232086743 59862654804904983348130115)
  ·
    refine ⟨89793982207357475022195173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59862654804904983348130115 89793982207357475022195173)
    ·
      refine ⟨16836371663879526566661595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89793982207357475022195173 16836371663879526566661595)
      ·
        refine ⟨25254557495819289849992393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16836371663879526566661595 25254557495819289849992393)
        ·
          refine ⟨18940918121864467387494295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25254557495819289849992393 18940918121864467387494295)
          ·
            refine ⟨28411377182796701081241443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18940918121864467387494295 28411377182796701081241443)
            ·
              refine ⟨42617065774195051621862165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28411377182796701081241443 42617065774195051621862165)
              ·
                refine ⟨1997674958165393044774789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42617065774195051621862165 1997674958165393044774789)
                ·
                  refine ⟨374564054656011195895273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1997674958165393044774789 374564054656011195895273)
                  ·
                    rfl

theorem cell21_1641287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 4].length) (baseStart_1641287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1641287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1641287 prefixEnd_1641287 := by exact prefixLift 1641287
  have htrace : WordTrace (prefixWord ++ tailWord_1641287) baseStart_1641287 baseEnd_1641287 := by
    simpa [prefixWord, tailWord_1641287, baseEnd_1641287] using wordTrace_append hprefix tailTrace_1641287
  have hstable : (prefixWord ++ tailWord_1641287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641287).length < 2 ^ (prefixWord ++ tailWord_1641287).sum := by decide
  have hdescent : baseEnd_1641287 < baseStart_1641287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641383 : List Nat := [1, 1, 6, 1, 3, 1, 2, 3, 3]
def baseStart_1641383 : Nat := 118140960795 + 1641383 * 2 ^ 59
def prefixEnd_1641383 : Nat := 4983230072969 + 3 ^ 40 * 1641383 * 2
def baseEnd_1641383 : Nat := 374585963163936362295077

theorem tailTrace_1641383 : CollatzResearch.WordTrace tailWord_1641383 prefixEnd_1641383 374585963163936362295077 := by
  unfold tailWord_1641383
  simp only [CollatzResearch.WordTrace]
  refine ⟨59866156212557191743624803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39910770808371461162416535 59866156212557191743624803)
  ·
    refine ⟨89799234318835787615437205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59866156212557191743624803 89799234318835787615437205)
    ·
      refine ⟨4209339108695427544473619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89799234318835787615437205 4209339108695427544473619)
      ·
        refine ⟨6314008663043141316710429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4209339108695427544473619 6314008663043141316710429)
        ·
          refine ⟨2367753248641177993766411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6314008663043141316710429 2367753248641177993766411)
          ·
            refine ⟨3551629872961766990649617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2367753248641177993766411 3551629872961766990649617)
            ·
              refine ⟨2663722404721325242987213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3551629872961766990649617 2663722404721325242987213)
              ·
                refine ⟨998895901770496966120205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2663722404721325242987213 998895901770496966120205)
                ·
                  refine ⟨374585963163936362295077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 998895901770496966120205 374585963163936362295077)
                  ·
                    rfl

theorem cell21_1641383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3, 3].length) (baseStart_1641383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1641383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1641383 prefixEnd_1641383 := by exact prefixLift 1641383
  have htrace : WordTrace (prefixWord ++ tailWord_1641383) baseStart_1641383 baseEnd_1641383 := by
    simpa [prefixWord, tailWord_1641383, baseEnd_1641383] using wordTrace_append hprefix tailTrace_1641383
  have hstable : (prefixWord ++ tailWord_1641383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641383).length < 2 ^ (prefixWord ++ tailWord_1641383).sum := by decide
  have hdescent : baseEnd_1641383 < baseStart_1641383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641408 : List Nat := [2, 1, 1, 2, 3, 3, 1, 3, 5]
def baseStart_1641408 : Nat := 118140960795 + 1641408 * 2 ^ 59
def prefixEnd_1641408 : Nat := 4983230072969 + 3 ^ 40 * 1641408 * 2
def baseEnd_1641408 : Nat := 374591668504541874378359

theorem tailTrace_1641408 : CollatzResearch.WordTrace tailWord_1641408 prefixEnd_1641408 374591668504541874378359 := by
  unfold tailWord_1641408
  simp only [CollatzResearch.WordTrace]
  refine ⟨29933534018733310506642439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39911378691644414008856585 29933534018733310506642439)
  ·
    refine ⟨44900301028099965759963659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29933534018733310506642439 44900301028099965759963659)
    ·
      refine ⟨67350451542149948639945489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44900301028099965759963659 67350451542149948639945489)
      ·
        refine ⟨50512838656612461479959117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67350451542149948639945489 50512838656612461479959117)
        ·
          refine ⟨18942314496229673054984669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50512838656612461479959117 18942314496229673054984669)
          ·
            refine ⟨7103367936086127395619251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18942314496229673054984669 7103367936086127395619251)
            ·
              refine ⟨10655051904129191093428877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7103367936086127395619251 10655051904129191093428877)
              ·
                refine ⟨3995644464048446660035829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10655051904129191093428877 3995644464048446660035829)
                ·
                  refine ⟨374591668504541874378359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3995644464048446660035829 374591668504541874378359)
                  ·
                    rfl

theorem cell21_1641408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 5].length) (baseStart_1641408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1641408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1641408 prefixEnd_1641408 := by exact prefixLift 1641408
  have htrace : WordTrace (prefixWord ++ tailWord_1641408) baseStart_1641408 baseEnd_1641408 := by
    simpa [prefixWord, tailWord_1641408, baseEnd_1641408] using wordTrace_append hprefix tailTrace_1641408
  have hstable : (prefixWord ++ tailWord_1641408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641408).length < 2 ^ (prefixWord ++ tailWord_1641408).sum := by decide
  have hdescent : baseEnd_1641408 < baseStart_1641408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641473 : List Nat := [1, 2, 4, 1, 2, 4, 2, 1, 4]
def baseStart_1641473 : Nat := 118140960795 + 1641473 * 2 ^ 59
def prefixEnd_1641473 : Nat := 4983230072969 + 3 ^ 40 * 1641473 * 2
def baseEnd_1641473 : Nat := 374606502390116205794893

theorem tailTrace_1641473 : CollatzResearch.WordTrace tailWord_1641473 prefixEnd_1641473 374606502390116205794893 := by
  unfold tailWord_1641473
  simp only [CollatzResearch.WordTrace]
  refine ⟨59869438782231137114401073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39912959188154091409600715 59869438782231137114401073)
  ·
    refine ⟨44902079086673352835800805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59869438782231137114401073 44902079086673352835800805)
    ·
      refine ⟨8419139828751253656712651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44902079086673352835800805 8419139828751253656712651)
      ·
        refine ⟨12628709743126880485068977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8419139828751253656712651 12628709743126880485068977)
        ·
          refine ⟨9471532307345160363801733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12628709743126880485068977 9471532307345160363801733)
          ·
            refine ⟨1775912307627217568212825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9471532307345160363801733 1775912307627217568212825)
            ·
              refine ⟨1331934230720413176159619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1775912307627217568212825 1331934230720413176159619)
              ·
                refine ⟨1997901346080619764239429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1331934230720413176159619 1997901346080619764239429)
                ·
                  refine ⟨374606502390116205794893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1997901346080619764239429 374606502390116205794893)
                  ·
                    rfl

theorem cell21_1641473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 4].length) (baseStart_1641473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1641473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1641473 prefixEnd_1641473 := by exact prefixLift 1641473
  have htrace : WordTrace (prefixWord ++ tailWord_1641473) baseStart_1641473 baseEnd_1641473 := by
    simpa [prefixWord, tailWord_1641473, baseEnd_1641473] using wordTrace_append hprefix tailTrace_1641473
  have hstable : (prefixWord ++ tailWord_1641473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641473).length < 2 ^ (prefixWord ++ tailWord_1641473).sum := by decide
  have hdescent : baseEnd_1641473 < baseStart_1641473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641515 : List Nat := [1, 1, 1, 1, 2, 1, 8, 2, 4]
def baseStart_1641515 : Nat := 118140960795 + 1641515 * 2 ^ 59
def prefixEnd_1641515 : Nat := 4983230072969 + 3 ^ 40 * 1641515 * 2
def baseEnd_1641515 : Nat := 374616087362333466094807

theorem tailTrace_1641515 : CollatzResearch.WordTrace tailWord_1641515 prefixEnd_1641515 374616087362333466094807 := by
  unfold tailWord_1641515
  simp only [CollatzResearch.WordTrace]
  refine ⟨59870970648078978287429999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39913980432052652191619999 59870970648078978287429999)
  ·
    refine ⟨89806455972118467431144999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59870970648078978287429999 89806455972118467431144999)
    ·
      refine ⟨134709683958177701146717499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89806455972118467431144999 134709683958177701146717499)
      ·
        refine ⟨202064525937266551720076249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134709683958177701146717499 202064525937266551720076249)
        ·
          refine ⟨151548394452949913790057187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202064525937266551720076249 151548394452949913790057187)
          ·
            refine ⟨227322591679424870685085781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151548394452949913790057187 227322591679424870685085781)
            ·
              refine ⟨2663936621243260203340849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 227322591679424870685085781 2663936621243260203340849)
              ·
                refine ⟨1997952465932445152505637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2663936621243260203340849 1997952465932445152505637)
                ·
                  refine ⟨374616087362333466094807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1997952465932445152505637 374616087362333466094807)
                  ·
                    rfl

theorem cell21_1641515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 4].length) (baseStart_1641515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1641515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1641515 prefixEnd_1641515 := by exact prefixLift 1641515
  have htrace : WordTrace (prefixWord ++ tailWord_1641515) baseStart_1641515 baseEnd_1641515 := by
    simpa [prefixWord, tailWord_1641515, baseEnd_1641515] using wordTrace_append hprefix tailTrace_1641515
  have hstable : (prefixWord ++ tailWord_1641515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641515).length < 2 ^ (prefixWord ++ tailWord_1641515).sum := by decide
  have hdescent : baseEnd_1641515 < baseStart_1641515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641518 : List Nat := [4, 1, 3, 1, 1, 1, 3, 4, 3]
def baseStart_1641518 : Nat := 118140960795 + 1641518 * 2 ^ 59
def prefixEnd_1641518 : Nat := 4983230072969 + 3 ^ 40 * 1641518 * 2
def baseEnd_1641518 : Nat := 374616772003206127544801

theorem tailTrace_1641518 : CollatzResearch.WordTrace tailWord_1641518 prefixEnd_1641518 374616772003206127544801 := by
  unfold tailWord_1641518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7483885008383513724973651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39914053378045406533192805 7483885008383513724973651)
  ·
    refine ⟨11225827512575270587460477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7483885008383513724973651 11225827512575270587460477)
    ·
      refine ⟨4209685317215726470297679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11225827512575270587460477 4209685317215726470297679)
      ·
        refine ⟨6314527975823589705446519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4209685317215726470297679 6314527975823589705446519)
        ·
          refine ⟨9471791963735384558169779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6314527975823589705446519 9471791963735384558169779)
          ·
            refine ⟨14207687945603076837254669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9471791963735384558169779 14207687945603076837254669)
            ·
              refine ⟨5327882979601153813970501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14207687945603076837254669 5327882979601153813970501)
              ·
                refine ⟨998978058675216340119469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5327882979601153813970501 998978058675216340119469)
                ·
                  refine ⟨374616772003206127544801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 998978058675216340119469 374616772003206127544801)
                  ·
                    rfl

theorem cell21_1641518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_1641518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1641518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1641518 prefixEnd_1641518 := by exact prefixLift 1641518
  have htrace : WordTrace (prefixWord ++ tailWord_1641518) baseStart_1641518 baseEnd_1641518 := by
    simpa [prefixWord, tailWord_1641518, baseEnd_1641518] using wordTrace_append hprefix tailTrace_1641518
  have hstable : (prefixWord ++ tailWord_1641518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641518).length < 2 ^ (prefixWord ++ tailWord_1641518).sum := by decide
  have hdescent : baseEnd_1641518 < baseStart_1641518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641566 : List Nat := [4, 4, 1, 1, 1, 1, 3, 2, 4]
def baseStart_1641566 : Nat := 118140960795 + 1641566 * 2 ^ 59
def prefixEnd_1641566 : Nat := 4983230072969 + 3 ^ 40 * 1641566 * 2
def baseEnd_1641566 : Nat := 374627726257168710744703

theorem tailTrace_1641566 : CollatzResearch.WordTrace tailWord_1641566 prefixEnd_1641566 374627726257168710744703 := by
  unfold tailWord_1641566
  simp only [CollatzResearch.WordTrace]
  refine ⟨7484103846361776749692069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39915220513929475998357701 7484103846361776749692069)
  ·
    refine ⟨1403269471192833140567263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7484103846361776749692069 1403269471192833140567263)
    ·
      refine ⟨2104904206789249710850895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1403269471192833140567263 2104904206789249710850895)
      ·
        refine ⟨3157356310183874566276343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2104904206789249710850895 3157356310183874566276343)
        ·
          refine ⟨4736034465275811849414515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3157356310183874566276343 4736034465275811849414515)
          ·
            refine ⟨7104051697913717774121773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4736034465275811849414515 7104051697913717774121773)
            ·
              refine ⟨2664019386717644165295665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7104051697913717774121773 2664019386717644165295665)
              ·
                refine ⟨1998014540038233123971749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2664019386717644165295665 1998014540038233123971749)
                ·
                  refine ⟨374627726257168710744703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1998014540038233123971749 374627726257168710744703)
                  ·
                    rfl

theorem cell21_1641566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_1641566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1641566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1641566 prefixEnd_1641566 := by exact prefixLift 1641566
  have htrace : WordTrace (prefixWord ++ tailWord_1641566) baseStart_1641566 baseEnd_1641566 := by
    simpa [prefixWord, tailWord_1641566, baseEnd_1641566] using wordTrace_append hprefix tailTrace_1641566
  have hstable : (prefixWord ++ tailWord_1641566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641566).length < 2 ^ (prefixWord ++ tailWord_1641566).sum := by decide
  have hdescent : baseEnd_1641566 < baseStart_1641566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641577 : List Nat := [1, 2, 1, 1, 1, 6, 2, 4, 3]
def baseStart_1641577 : Nat := 118140960795 + 1641577 * 2 ^ 59
def prefixEnd_1641577 : Nat := 4983230072969 + 3 ^ 40 * 1641577 * 2
def baseEnd_1641577 : Nat := 374630236607035136061347

theorem tailTrace_1641577 : CollatzResearch.WordTrace tailWord_1641577 prefixEnd_1641577 374630236607035136061347 := by
  unfold tailWord_1641577
  simp only [CollatzResearch.WordTrace]
  refine ⟨59873231973854362876186985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39915487982569575250791323 59873231973854362876186985)
  ·
    refine ⟨44904923980390772157140239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59873231973854362876186985 44904923980390772157140239)
    ·
      refine ⟨67357385970586158235710359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44904923980390772157140239 67357385970586158235710359)
      ·
        refine ⟨101036078955879237353565539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67357385970586158235710359 101036078955879237353565539)
        ·
          refine ⟨151554118433818856030348309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101036078955879237353565539 151554118433818856030348309)
          ·
            refine ⟨7104099301585258876422577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 151554118433818856030348309 7104099301585258876422577)
            ·
              refine ⟨5328074476188944157316933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7104099301585258876422577 5328074476188944157316933)
              ·
                refine ⟨999013964285427029496925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5328074476188944157316933 999013964285427029496925)
                ·
                  refine ⟨374630236607035136061347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 999013964285427029496925 374630236607035136061347)
                  ·
                    rfl

theorem cell21_1641577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4, 3].length) (baseStart_1641577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1641577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1641577 prefixEnd_1641577 := by exact prefixLift 1641577
  have htrace : WordTrace (prefixWord ++ tailWord_1641577) baseStart_1641577 baseEnd_1641577 := by
    simpa [prefixWord, tailWord_1641577, baseEnd_1641577] using wordTrace_append hprefix tailTrace_1641577
  have hstable : (prefixWord ++ tailWord_1641577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641577).length < 2 ^ (prefixWord ++ tailWord_1641577).sum := by decide
  have hdescent : baseEnd_1641577 < baseStart_1641577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641619 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 7]
def baseStart_1641619 : Nat := 118140960795 + 1641619 * 2 ^ 59
def prefixEnd_1641619 : Nat := 4983230072969 + 3 ^ 40 * 1641619 * 2
def baseEnd_1641619 : Nat := 374639821579252396361261

theorem tailTrace_1641619 : CollatzResearch.WordTrace tailWord_1641619 prefixEnd_1641619 374639821579252396361261 := by
  unfold tailWord_1641619
  simp only [CollatzResearch.WordTrace]
  refine ⟨59874763839702204049215911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39916509226468136032810607 59874763839702204049215911)
  ·
    refine ⟨89812145759553306073823867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59874763839702204049215911 89812145759553306073823867)
    ·
      refine ⟨134718218639329959110735801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89812145759553306073823867 134718218639329959110735801)
      ·
        refine ⟨101038663979497469333051851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134718218639329959110735801 101038663979497469333051851)
        ·
          refine ⟨151557995969246203999577777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101038663979497469333051851 151557995969246203999577777)
          ·
            refine ⟨113668496976934652999683333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151557995969246203999577777 113668496976934652999683333)
            ·
              refine ⟨21312843183175247437440625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113668496976934652999683333 21312843183175247437440625)
              ·
                refine ⟨15984632387381435578080469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21312843183175247437440625 15984632387381435578080469)
                ·
                  refine ⟨374639821579252396361261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15984632387381435578080469 374639821579252396361261)
                  ·
                    rfl

theorem cell21_1641619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 7].length) (baseStart_1641619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1641619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1641619 prefixEnd_1641619 := by exact prefixLift 1641619
  have htrace : WordTrace (prefixWord ++ tailWord_1641619) baseStart_1641619 baseEnd_1641619 := by
    simpa [prefixWord, tailWord_1641619, baseEnd_1641619] using wordTrace_append hprefix tailTrace_1641619
  have hstable : (prefixWord ++ tailWord_1641619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641619).length < 2 ^ (prefixWord ++ tailWord_1641619).sum := by decide
  have hdescent : baseEnd_1641619 < baseStart_1641619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641642 : List Nat := [3, 1, 5, 1, 1, 3, 2, 1, 4]
def baseStart_1641642 : Nat := 118140960795 + 1641642 * 2 ^ 59
def prefixEnd_1641642 : Nat := 4983230072969 + 3 ^ 40 * 1641642 * 2
def baseEnd_1641642 : Nat := 374645070492609467477881

theorem tailTrace_1641642 : CollatzResearch.WordTrace tailWord_1641642 prefixEnd_1641642 374645070492609467477881 := by
  unfold tailWord_1641642
  simp only [CollatzResearch.WordTrace]
  refine ⟨14968900679654719744325795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39917068479079252651535453 14968900679654719744325795)
  ·
    refine ⟨22453351019482079616488693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14968900679654719744325795 22453351019482079616488693)
    ·
      refine ⟨2105001658076444964045815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22453351019482079616488693 2105001658076444964045815)
      ·
        refine ⟨3157502487114667446068723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2105001658076444964045815 3157502487114667446068723)
        ·
          refine ⟨4736253730672001169103085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3157502487114667446068723 4736253730672001169103085)
          ·
            refine ⟨1776095149002000438413657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4736253730672001169103085 1776095149002000438413657)
            ·
              refine ⟨1332071361751500328810243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1776095149002000438413657 1332071361751500328810243)
              ·
                refine ⟨1998107042627250493215365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1332071361751500328810243 1998107042627250493215365)
                ·
                  refine ⟨374645070492609467477881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1998107042627250493215365 374645070492609467477881)
                  ·
                    rfl

theorem cell21_1641642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_1641642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1641642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1641642 prefixEnd_1641642 := by exact prefixLift 1641642
  have htrace : WordTrace (prefixWord ++ tailWord_1641642) baseStart_1641642 baseEnd_1641642 := by
    simpa [prefixWord, tailWord_1641642, baseEnd_1641642] using wordTrace_append hprefix tailTrace_1641642
  have hstable : (prefixWord ++ tailWord_1641642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641642).length < 2 ^ (prefixWord ++ tailWord_1641642).sum := by decide
  have hdescent : baseEnd_1641642 < baseStart_1641642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641729 : List Nat := [1, 2, 4, 1, 1, 3, 1, 5, 3]
def baseStart_1641729 : Nat := 118140960795 + 1641729 * 2 ^ 59
def prefixEnd_1641729 : Nat := 4983230072969 + 3 ^ 40 * 1641729 * 2
def baseEnd_1641729 : Nat := 374664925077916649527703

theorem tailTrace_1641729 : CollatzResearch.WordTrace tailWord_1641729 prefixEnd_1641729 374664925077916649527703 := by
  unfold tailWord_1641729
  simp only [CollatzResearch.WordTrace]
  refine ⟨59878775869303692835720241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39919183912869128557146827 59878775869303692835720241)
  ·
    refine ⟨44909081901977769626790181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59878775869303692835720241 44909081901977769626790181)
    ·
      refine ⟨8420452856620831805023159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44909081901977769626790181 8420452856620831805023159)
      ·
        refine ⟨12630679284931247707534739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8420452856620831805023159 12630679284931247707534739)
        ·
          refine ⟨18946018927396871561302109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12630679284931247707534739 18946018927396871561302109)
          ·
            refine ⟨7104757097773826835488291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18946018927396871561302109 7104757097773826835488291)
            ·
              refine ⟨10657135646660740253232437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7104757097773826835488291 10657135646660740253232437)
              ·
                refine ⟨999106466874444398740541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10657135646660740253232437 999106466874444398740541)
                ·
                  refine ⟨374664925077916649527703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 999106466874444398740541 374664925077916649527703)
                  ·
                    rfl

theorem cell21_1641729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5, 3].length) (baseStart_1641729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1641729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1641729 prefixEnd_1641729 := by exact prefixLift 1641729
  have htrace : WordTrace (prefixWord ++ tailWord_1641729) baseStart_1641729 baseEnd_1641729 := by
    simpa [prefixWord, tailWord_1641729, baseEnd_1641729] using wordTrace_append hprefix tailTrace_1641729
  have hstable : (prefixWord ++ tailWord_1641729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641729).length < 2 ^ (prefixWord ++ tailWord_1641729).sum := by decide
  have hdescent : baseEnd_1641729 < baseStart_1641729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641909 : List Nat := [1, 3, 3, 2, 2, 2, 8]
def baseStart_1641909 : Nat := 118140960795 + 1641909 * 2 ^ 59
def prefixEnd_1641909 : Nat := 4983230072969 + 3 ^ 40 * 1641909 * 2
def baseEnd_1641909 : Nat := 41634000392252926280815

theorem tailTrace_1641909 : CollatzResearch.WordTrace tailWord_1641909 prefixEnd_1641909 41634000392252926280815 := by
  unfold tailWord_1641909
  simp only [CollatzResearch.WordTrace]
  refine ⟨59885341008651583577272781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39923560672434389051515187 59885341008651583577272781)
  ·
    refine ⟨22457002878244343841477293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59885341008651583577272781 22457002878244343841477293)
    ·
      refine ⟨8421376079341628940553985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22457002878244343841477293 8421376079341628940553985)
      ·
        refine ⟨6316032059506221705415489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8421376079341628940553985 6316032059506221705415489)
        ·
          refine ⟨4737024044629666279061617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6316032059506221705415489 4737024044629666279061617)
          ·
            refine ⟨3552768033472249709296213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4737024044629666279061617 3552768033472249709296213)
            ·
              refine ⟨41634000392252926280815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3552768033472249709296213 41634000392252926280815)
              ·
                rfl

theorem cell21_1641909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 8].length) (baseStart_1641909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1641909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1641909 prefixEnd_1641909 := by exact prefixLift 1641909
  have htrace : WordTrace (prefixWord ++ tailWord_1641909) baseStart_1641909 baseEnd_1641909 := by
    simpa [prefixWord, tailWord_1641909, baseEnd_1641909] using wordTrace_append hprefix tailTrace_1641909
  have hstable : (prefixWord ++ tailWord_1641909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641909).length < 2 ^ (prefixWord ++ tailWord_1641909).sum := by decide
  have hdescent : baseEnd_1641909 < baseStart_1641909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641923 : List Nat := [1, 1, 1, 3, 1, 1, 5, 3, 5]
def baseStart_1641923 : Nat := 118140960795 + 1641923 * 2 ^ 59
def prefixEnd_1641923 : Nat := 4983230072969 + 3 ^ 40 * 1641923 * 2
def baseEnd_1641923 : Nat := 374709198521015423293973

theorem tailTrace_1641923 : CollatzResearch.WordTrace tailWord_1641923 prefixEnd_1641923 374709198521015423293973 := by
  unfold tailWord_1641923
  simp only [CollatzResearch.WordTrace]
  refine ⟨59885851630600863968282423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39923901087067242645521615 59885851630600863968282423)
  ·
    refine ⟨89828777445901295952423635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59885851630600863968282423 89828777445901295952423635)
    ·
      refine ⟨134743166168851943928635453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89828777445901295952423635 134743166168851943928635453)
      ·
        refine ⟨50528687313319478973238295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134743166168851943928635453 50528687313319478973238295)
        ·
          refine ⟨75793030969979218459857443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50528687313319478973238295 75793030969979218459857443)
          ·
            refine ⟨113689546454968827689786165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75793030969979218459857443 113689546454968827689786165)
            ·
              refine ⟨10658394980153327595917453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113689546454968827689786165 10658394980153327595917453)
              ·
                refine ⟨3996898117557497848469045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10658394980153327595917453 3996898117557497848469045)
                ·
                  refine ⟨374709198521015423293973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3996898117557497848469045 374709198521015423293973)
                  ·
                    rfl

theorem cell21_1641923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 5].length) (baseStart_1641923 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1641923 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1641923 prefixEnd_1641923 := by exact prefixLift 1641923
  have htrace : WordTrace (prefixWord ++ tailWord_1641923) baseStart_1641923 baseEnd_1641923 := by
    simpa [prefixWord, tailWord_1641923, baseEnd_1641923] using wordTrace_append hprefix tailTrace_1641923
  have hstable : (prefixWord ++ tailWord_1641923).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641923).length < 2 ^ (prefixWord ++ tailWord_1641923).sum := by decide
  have hdescent : baseEnd_1641923 < baseStart_1641923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641968 : List Nat := [2, 1, 1, 1, 3, 4, 9]
def baseStart_1641968 : Nat := 118140960795 + 1641968 * 2 ^ 59
def prefixEnd_1641968 : Nat := 4983230072969 + 3 ^ 40 * 1641968 * 2
def baseEnd_1641968 : Nat := 41635496459345038338209

theorem tailTrace_1641968 : CollatzResearch.WordTrace tailWord_1641968 prefixEnd_1641968 41635496459345038338209 := by
  unfold tailWord_1641968
  simp only [CollatzResearch.WordTrace]
  refine ⟨29943746457718918326835279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39924995276958557769113705 29943746457718918326835279)
  ·
    refine ⟨44915619686578377490252919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29943746457718918326835279 44915619686578377490252919)
    ·
      refine ⟨67373429529867566235379379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44915619686578377490252919 67373429529867566235379379)
      ·
        refine ⟨101060144294801349353069069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67373429529867566235379379 101060144294801349353069069)
        ·
          refine ⟨37897554110550506007400901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101060144294801349353069069 37897554110550506007400901)
          ·
            refine ⟨7105791395728219876387669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37897554110550506007400901 7105791395728219876387669)
            ·
              refine ⟨41635496459345038338209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7105791395728219876387669 41635496459345038338209)
              ·
                rfl

theorem cell21_1641968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 9].length) (baseStart_1641968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1641968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1641968 prefixEnd_1641968 := by exact prefixLift 1641968
  have htrace : WordTrace (prefixWord ++ tailWord_1641968) baseStart_1641968 baseEnd_1641968 := by
    simpa [prefixWord, tailWord_1641968, baseEnd_1641968] using wordTrace_append hprefix tailTrace_1641968
  have hstable : (prefixWord ++ tailWord_1641968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641968).length < 2 ^ (prefixWord ++ tailWord_1641968).sum := by decide
  have hdescent : baseEnd_1641968 < baseStart_1641968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641988 : List Nat := [2, 3, 2, 3, 2, 1, 1, 3, 4]
def baseStart_1641988 : Nat := 118140960795 + 1641988 * 2 ^ 59
def prefixEnd_1641988 : Nat := 4983230072969 + 3 ^ 40 * 1641988 * 2
def baseEnd_1641988 : Nat := 374724032406589754710507

theorem tailTrace_1641988 : CollatzResearch.WordTrace tailWord_1641988 prefixEnd_1641988 374724032406589754710507 := by
  unfold tailWord_1641988
  simp only [CollatzResearch.WordTrace]
  refine ⟨29944111187682690034699309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39925481583576920046265745 29944111187682690034699309)
  ·
    refine ⟨11229041695381008763012241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29944111187682690034699309 11229041695381008763012241)
    ·
      refine ⟨8421781271535756572259181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11229041695381008763012241 8421781271535756572259181)
      ·
        refine ⟨3158167976825908714597193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8421781271535756572259181 3158167976825908714597193)
        ·
          refine ⟨2368625982619431535947895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3158167976825908714597193 2368625982619431535947895)
          ·
            refine ⟨3552938973929147303921843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2368625982619431535947895 3552938973929147303921843)
            ·
              refine ⟨5329408460893720955882765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3552938973929147303921843 5329408460893720955882765)
              ·
                refine ⟨1998528172835145358456037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5329408460893720955882765 1998528172835145358456037)
                ·
                  refine ⟨374724032406589754710507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1998528172835145358456037 374724032406589754710507)
                  ·
                    rfl

theorem cell21_1641988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_1641988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1641988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1641988 prefixEnd_1641988 := by exact prefixLift 1641988
  have htrace : WordTrace (prefixWord ++ tailWord_1641988) baseStart_1641988 baseEnd_1641988 := by
    simpa [prefixWord, tailWord_1641988, baseEnd_1641988] using wordTrace_append hprefix tailTrace_1641988
  have hstable : (prefixWord ++ tailWord_1641988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641988).length < 2 ^ (prefixWord ++ tailWord_1641988).sum := by decide
  have hdescent : baseEnd_1641988 < baseStart_1641988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642126 : List Nat := [4, 1, 1, 3, 1, 4, 1, 3, 3]
def baseStart_1642126 : Nat := 118140960795 + 1642126 * 2 ^ 59
def prefixEnd_1642126 : Nat := 4983230072969 + 3 ^ 40 * 1642126 * 2
def baseEnd_1642126 : Nat := 374755525886732181410225

theorem tailTrace_1642126 : CollatzResearch.WordTrace tailWord_1642126 prefixEnd_1642126 374755525886732181410225 := by
  unfold tailWord_1642126
  simp only [CollatzResearch.WordTrace]
  refine ⟨7486656956108178704740279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39928837099243619758614821 7486656956108178704740279)
  ·
    refine ⟨11229985434162268057110419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7486656956108178704740279 11229985434162268057110419)
    ·
      refine ⟨16844978151243402085665629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11229985434162268057110419 16844978151243402085665629)
      ·
        refine ⟨6316866806716275782124611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16844978151243402085665629 6316866806716275782124611)
        ·
          refine ⟨9475300210074413673186917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6316866806716275782124611 9475300210074413673186917)
          ·
            refine ⟨1776618789388952563722547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9475300210074413673186917 1776618789388952563722547)
            ·
              refine ⟨2664928184083428845583821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1776618789388952563722547 2664928184083428845583821)
              ·
                refine ⟨999348069031285817093933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2664928184083428845583821 999348069031285817093933)
                ·
                  refine ⟨374755525886732181410225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 999348069031285817093933 374755525886732181410225)
                  ·
                    rfl

theorem cell21_1642126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_1642126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1642126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1642126 prefixEnd_1642126 := by exact prefixLift 1642126
  have htrace : WordTrace (prefixWord ++ tailWord_1642126) baseStart_1642126 baseEnd_1642126 := by
    simpa [prefixWord, tailWord_1642126, baseEnd_1642126] using wordTrace_append hprefix tailTrace_1642126
  have hstable : (prefixWord ++ tailWord_1642126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642126).length < 2 ^ (prefixWord ++ tailWord_1642126).sum := by decide
  have hdescent : baseEnd_1642126 < baseStart_1642126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642143 : List Nat := [1, 1, 2, 7, 1, 1, 3, 2, 3]
def baseStart_1642143 : Nat := 118140960795 + 1642143 * 2 ^ 59
def prefixEnd_1642143 : Nat := 4983230072969 + 3 ^ 40 * 1642143 * 2
def baseEnd_1642143 : Nat := 374759405518343929626857

theorem tailTrace_1642143 : CollatzResearch.WordTrace tailWord_1642143 prefixEnd_1642143 374759405518343929626857 := by
  unfold tailWord_1642143
  simp only [CollatzResearch.WordTrace]
  refine ⟨59893875689803841541291083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39929250459869227694194055 59893875689803841541291083)
  ·
    refine ⟨89840813534705762311936625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59893875689803841541291083 89840813534705762311936625)
    ·
      refine ⟨67380610151029321733952469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89840813534705762311936625 67380610151029321733952469)
      ·
        refine ⟨1579233050414749728139511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 67380610151029321733952469 1579233050414749728139511)
        ·
          refine ⟨2368849575622124592209267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1579233050414749728139511 2368849575622124592209267)
          ·
            refine ⟨3553274363433186888313901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2368849575622124592209267 3553274363433186888313901)
            ·
              refine ⟨1332477886287445083117713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3553274363433186888313901 1332477886287445083117713)
              ·
                refine ⟨999358414715583812338285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1332477886287445083117713 999358414715583812338285)
                ·
                  refine ⟨374759405518343929626857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 999358414715583812338285 374759405518343929626857)
                  ·
                    rfl

theorem cell21_1642143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2, 3].length) (baseStart_1642143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1642143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1642143 prefixEnd_1642143 := by exact prefixLift 1642143
  have htrace : WordTrace (prefixWord ++ tailWord_1642143) baseStart_1642143 baseEnd_1642143 := by
    simpa [prefixWord, tailWord_1642143, baseEnd_1642143] using wordTrace_append hprefix tailTrace_1642143
  have hstable : (prefixWord ++ tailWord_1642143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642143).length < 2 ^ (prefixWord ++ tailWord_1642143).sum := by decide
  have hdescent : baseEnd_1642143 < baseStart_1642143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642202 : List Nat := [3, 1, 1, 2, 2, 5, 2, 2, 3]
def baseStart_1642202 : Nat := 118140960795 + 1642202 * 2 ^ 59
def prefixEnd_1642202 : Nat := 4983230072969 + 3 ^ 40 * 1642202 * 2
def baseEnd_1642202 : Nat := 374772870122172938143403

theorem tailTrace_1642202 : CollatzResearch.WordTrace tailWord_1642202 prefixEnd_1642202 374772870122172938143403 := by
  unfold tailWord_1642202
  simp only [CollatzResearch.WordTrace]
  refine ⟨14974006899147523654422215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39930685064393396411792573 14974006899147523654422215)
  ·
    refine ⟨22461010348721285481633323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14974006899147523654422215 22461010348721285481633323)
    ·
      refine ⟨33691515523081928222449985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22461010348721285481633323 33691515523081928222449985)
      ·
        refine ⟨25268636642311446166837489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33691515523081928222449985 25268636642311446166837489)
        ·
          refine ⟨18951477481733584625128117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25268636642311446166837489 18951477481733584625128117)
          ·
            refine ⟨1776701013912523558605761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18951477481733584625128117 1776701013912523558605761)
            ·
              refine ⟨1332525760434392668954321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1776701013912523558605761 1332525760434392668954321)
              ·
                refine ⟨999394320325794501715741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1332525760434392668954321 999394320325794501715741)
                ·
                  refine ⟨374772870122172938143403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 999394320325794501715741 374772870122172938143403)
                  ·
                    rfl

theorem cell21_1642202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2, 3].length) (baseStart_1642202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1642202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1642202 prefixEnd_1642202 := by exact prefixLift 1642202
  have htrace : WordTrace (prefixWord ++ tailWord_1642202) baseStart_1642202 baseEnd_1642202 := by
    simpa [prefixWord, tailWord_1642202, baseEnd_1642202] using wordTrace_append hprefix tailTrace_1642202
  have hstable : (prefixWord ++ tailWord_1642202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642202).length < 2 ^ (prefixWord ++ tailWord_1642202).sum := by decide
  have hdescent : baseEnd_1642202 < baseStart_1642202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642230 : List Nat := [5, 1, 1, 1, 1, 4, 3, 5]
def baseStart_1642230 : Nat := 118140960795 + 1642230 * 2 ^ 59
def prefixEnd_1642230 : Nat := 4983230072969 + 3 ^ 40 * 1642230 * 2
def baseEnd_1642230 : Nat := 124926420034550370558893

theorem tailTrace_1642230 : CollatzResearch.WordTrace tailWord_1642230 prefixEnd_1642230 124926420034550370558893 := by
  unfold tailWord_1642230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3743565552530540962481759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39931365893659103599805429 3743565552530540962481759)
  ·
    refine ⟨5615348328795811443722639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3743565552530540962481759 5615348328795811443722639)
    ·
      refine ⟨8423022493193717165583959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5615348328795811443722639 8423022493193717165583959)
      ·
        refine ⟨12634533739790575748375939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8423022493193717165583959 12634533739790575748375939)
        ·
          refine ⟨18951800609685863622563909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12634533739790575748375939 18951800609685863622563909)
          ·
            refine ⟨3553462614316099429230733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18951800609685863622563909 3553462614316099429230733)
            ·
              refine ⟨1332548480368537285961525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3553462614316099429230733 1332548480368537285961525)
              ·
                refine ⟨124926420034550370558893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1332548480368537285961525 124926420034550370558893)
                ·
                  rfl

theorem cell21_1642230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_1642230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1642230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1642230 prefixEnd_1642230 := by exact prefixLift 1642230
  have htrace : WordTrace (prefixWord ++ tailWord_1642230) baseStart_1642230 baseEnd_1642230 := by
    simpa [prefixWord, tailWord_1642230, baseEnd_1642230] using wordTrace_append hprefix tailTrace_1642230
  have hstable : (prefixWord ++ tailWord_1642230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642230).length < 2 ^ (prefixWord ++ tailWord_1642230).sum := by decide
  have hdescent : baseEnd_1642230 < baseStart_1642230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642272 : List Nat := [2, 1, 1, 5, 1, 1, 2, 8]
def baseStart_1642272 : Nat := 118140960795 + 1642272 * 2 ^ 59
def prefixEnd_1642272 : Nat := 4983230072969 + 3 ^ 40 * 1642272 * 2
def baseEnd_1642272 : Nat := 124929615025289457325531

theorem tailTrace_1642272 : CollatzResearch.WordTrace tailWord_1642272 prefixEnd_1642272 124929615025289457325531 := by
  unfold tailWord_1642272
  simp only [CollatzResearch.WordTrace]
  refine ⟨29949290353168248286368535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39932387137557664381824713 29949290353168248286368535)
  ·
    refine ⟨44923935529752372429552803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29949290353168248286368535 44923935529752372429552803)
    ·
      refine ⟨67385903294628558644329205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44923935529752372429552803 67385903294628558644329205)
      ·
        refine ⟨6317428433871427372905863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67385903294628558644329205 6317428433871427372905863)
        ·
          refine ⟨9476142650807141059358795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6317428433871427372905863 9476142650807141059358795)
          ·
            refine ⟨14214213976210711589038193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9476142650807141059358795 14214213976210711589038193)
            ·
              refine ⟨10660660482158033691778645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14214213976210711589038193 10660660482158033691778645)
              ·
                refine ⟨124929615025289457325531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10660660482158033691778645 124929615025289457325531)
                ·
                  rfl

theorem cell21_1642272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 8].length) (baseStart_1642272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1642272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1642272 prefixEnd_1642272 := by exact prefixLift 1642272
  have htrace : WordTrace (prefixWord ++ tailWord_1642272) baseStart_1642272 baseEnd_1642272 := by
    simpa [prefixWord, tailWord_1642272, baseEnd_1642272] using wordTrace_append hprefix tailTrace_1642272
  have hstable : (prefixWord ++ tailWord_1642272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642272).length < 2 ^ (prefixWord ++ tailWord_1642272).sum := by decide
  have hdescent : baseEnd_1642272 < baseStart_1642272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642289 : List Nat := [1, 2, 2, 3, 2, 2, 4, 5]
def baseStart_1642289 : Nat := 118140960795 + 1642289 * 2 ^ 59
def prefixEnd_1642289 : Nat := 4983230072969 + 3 ^ 40 * 1642289 * 2
def baseEnd_1642289 : Nat := 124930908235826706731075

theorem tailTrace_1642289 : CollatzResearch.WordTrace tailWord_1642289 prefixEnd_1642289 124930908235826706731075 := by
  unfold tailWord_1642289
  simp only [CollatzResearch.WordTrace]
  refine ⟨59899200747274908476105921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39932800498183272317403947 59899200747274908476105921)
  ·
    refine ⟨44924400560456181357079441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59899200747274908476105921 44924400560456181357079441)
    ·
      refine ⟨33693300420342136017809581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44924400560456181357079441 33693300420342136017809581)
      ·
        refine ⟨12634987657628301006678593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33693300420342136017809581 12634987657628301006678593)
        ·
          refine ⟨9476240743221225755008945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12634987657628301006678593 9476240743221225755008945)
          ·
            refine ⟨7107180557415919316256709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9476240743221225755008945 7107180557415919316256709)
            ·
              refine ⟨1332596354515484871798133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7107180557415919316256709 1332596354515484871798133)
              ·
                refine ⟨124930908235826706731075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1332596354515484871798133 124930908235826706731075)
                ·
                  rfl

theorem cell21_1642289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 5].length) (baseStart_1642289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1642289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1642289 prefixEnd_1642289 := by exact prefixLift 1642289
  have htrace : WordTrace (prefixWord ++ tailWord_1642289) baseStart_1642289 baseEnd_1642289 := by
    simpa [prefixWord, tailWord_1642289, baseEnd_1642289] using wordTrace_append hprefix tailTrace_1642289
  have hstable : (prefixWord ++ tailWord_1642289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642289).length < 2 ^ (prefixWord ++ tailWord_1642289).sum := by decide
  have hdescent : baseEnd_1642289 < baseStart_1642289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642348 : List Nat := [2, 2, 1, 1, 4, 2, 2, 7]
def baseStart_1642348 : Nat := 118140960795 + 1642348 * 2 ^ 59
def prefixEnd_1642348 : Nat := 4983230072969 + 3 ^ 40 * 1642348 * 2
def baseEnd_1642348 : Nat := 124935396437103042903257

theorem tailTrace_1642348 : CollatzResearch.WordTrace tailWord_1642348 prefixEnd_1642348 124935396437103042903257 := by
  unfold tailWord_1642348
  simp only [CollatzResearch.WordTrace]
  refine ⟨29950676327030580776251849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39934235102707441035002465 29950676327030580776251849)
  ·
    refine ⟨22463007245272935582188887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29950676327030580776251849 22463007245272935582188887)
    ·
      refine ⟨33694510867909403373283331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22463007245272935582188887 33694510867909403373283331)
      ·
        refine ⟨50541766301864105059924997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33694510867909403373283331 50541766301864105059924997)
        ·
          refine ⟨9476581181599519698735937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50541766301864105059924997 9476581181599519698735937)
          ·
            refine ⟨7107435886199639774051953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9476581181599519698735937 7107435886199639774051953)
            ·
              refine ⟨5330576914649729830538965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7107435886199639774051953 5330576914649729830538965)
              ·
                refine ⟨124935396437103042903257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5330576914649729830538965 124935396437103042903257)
                ·
                  rfl

theorem cell21_1642348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 7].length) (baseStart_1642348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1642348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1642348 prefixEnd_1642348 := by exact prefixLift 1642348
  have htrace : WordTrace (prefixWord ++ tailWord_1642348) baseStart_1642348 baseEnd_1642348 := by
    simpa [prefixWord, tailWord_1642348, baseEnd_1642348] using wordTrace_append hprefix tailTrace_1642348
  have hstable : (prefixWord ++ tailWord_1642348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642348).length < 2 ^ (prefixWord ++ tailWord_1642348).sum := by decide
  have hdescent : baseEnd_1642348 < baseStart_1642348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642396 : List Nat := [2, 2, 3, 3, 1, 2, 1, 2, 5]
def baseStart_1642396 : Nat := 118140960795 + 1642396 * 2 ^ 59
def prefixEnd_1642396 : Nat := 4983230072969 + 3 ^ 40 * 1642396 * 2
def baseEnd_1642396 : Nat := 374817143565271711909673

theorem tailTrace_1642396 : CollatzResearch.WordTrace tailWord_1642396 prefixEnd_1642396 374817143565271711909673 := by
  unfold tailWord_1642396
  simp only [CollatzResearch.WordTrace]
  refine ⟨29951551678943632875125521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39935402238591510500167361 29951551678943632875125521)
  ·
    refine ⟨22463663759207724656344141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29951551678943632875125521 22463663759207724656344141)
    ·
      refine ⟨8423873909702896746129053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22463663759207724656344141 8423873909702896746129053)
      ·
        refine ⟨3158952716138586279798395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8423873909702896746129053 3158952716138586279798395)
        ·
          refine ⟨4738429074207879419697593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3158952716138586279798395 4738429074207879419697593)
          ·
            refine ⟨3553821805655909564773195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4738429074207879419697593 3553821805655909564773195)
            ·
              refine ⟨5330732708483864347159793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3553821805655909564773195 5330732708483864347159793)
              ·
                refine ⟨3998049531362898260369845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5330732708483864347159793 3998049531362898260369845)
                ·
                  refine ⟨374817143565271711909673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3998049531362898260369845 374817143565271711909673)
                  ·
                    rfl

theorem cell21_1642396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_1642396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1642396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1642396 prefixEnd_1642396 := by exact prefixLift 1642396
  have htrace : WordTrace (prefixWord ++ tailWord_1642396) baseStart_1642396 baseEnd_1642396 := by
    simpa [prefixWord, tailWord_1642396, baseEnd_1642396] using wordTrace_append hprefix tailTrace_1642396
  have hstable : (prefixWord ++ tailWord_1642396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642396).length < 2 ^ (prefixWord ++ tailWord_1642396).sum := by decide
  have hdescent : baseEnd_1642396 < baseStart_1642396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642458 : List Nat := [3, 1, 1, 2, 5, 2, 2, 5]
def baseStart_1642458 : Nat := 118140960795 + 1642458 * 2 ^ 59
def prefixEnd_1642458 : Nat := 4983230072969 + 3 ^ 40 * 1642458 * 2
def baseEnd_1642458 : Nat := 124943764269991127292071

theorem tailTrace_1642458 : CollatzResearch.WordTrace tailWord_1642458 prefixEnd_1642458 124943764269991127292071 := by
  unfold tailWord_1642458
  simp only [CollatzResearch.WordTrace]
  refine ⟨14976341170915662584752007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39936909789108433559338685 14976341170915662584752007)
  ·
    refine ⟨22464511756373493877128011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14976341170915662584752007 22464511756373493877128011)
    ·
      refine ⟨33696767634560240815692017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22464511756373493877128011 33696767634560240815692017)
      ·
        refine ⟨25272575725920180611769013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33696767634560240815692017 25272575725920180611769013)
        ·
          refine ⟨2369303974305016932353345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25272575725920180611769013 2369303974305016932353345)
          ·
            refine ⟨1776977980728762699265009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2369303974305016932353345 1776977980728762699265009)
            ·
              refine ⟨1332733485546572024448757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1776977980728762699265009 1332733485546572024448757)
              ·
                refine ⟨124943764269991127292071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1332733485546572024448757 124943764269991127292071)
                ·
                  rfl

theorem cell21_1642458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 5].length) (baseStart_1642458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1642458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1642458 prefixEnd_1642458 := by exact prefixLift 1642458
  have htrace : WordTrace (prefixWord ++ tailWord_1642458) baseStart_1642458 baseEnd_1642458 := by
    simpa [prefixWord, tailWord_1642458, baseEnd_1642458] using wordTrace_append hprefix tailTrace_1642458
  have hstable : (prefixWord ++ tailWord_1642458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642458).length < 2 ^ (prefixWord ++ tailWord_1642458).sum := by decide
  have hdescent : baseEnd_1642458 < baseStart_1642458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642489 : List Nat := [1, 2, 1, 3, 1, 5, 3, 2, 3]
def baseStart_1642489 : Nat := 118140960795 + 1642489 * 2 ^ 59
def prefixEnd_1642489 : Nat := 4983230072969 + 3 ^ 40 * 1642489 * 2
def baseEnd_1642489 : Nat := 374838367432324216859483

theorem tailTrace_1642489 : CollatzResearch.WordTrace tailWord_1642489 prefixEnd_1642489 374838367432324216859483 := by
  unfold tailWord_1642489
  simp only [CollatzResearch.WordTrace]
  refine ⟨59906495346550342633386521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39937663564366895088924347 59906495346550342633386521)
  ·
    refine ⟨44929871509912756975039891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59906495346550342633386521 44929871509912756975039891)
    ·
      refine ⟨67394807264869135462559837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44929871509912756975039891 67394807264869135462559837)
      ·
        refine ⟨25273052724325925798459939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67394807264869135462559837 25273052724325925798459939)
        ·
          refine ⟨37909579086488888697689909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25273052724325925798459939 37909579086488888697689909)
          ·
            refine ⟨3554023039358333315408429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37909579086488888697689909 3554023039358333315408429)
            ·
              refine ⟨1332758639759374993278161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3554023039358333315408429 1332758639759374993278161)
              ·
                refine ⟨999568979819531244958621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1332758639759374993278161 999568979819531244958621)
                ·
                  refine ⟨374838367432324216859483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 999568979819531244958621 374838367432324216859483)
                  ·
                    rfl

theorem cell21_1642489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2, 3].length) (baseStart_1642489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1642489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1642489 prefixEnd_1642489 := by exact prefixLift 1642489
  have htrace : WordTrace (prefixWord ++ tailWord_1642489) baseStart_1642489 baseEnd_1642489 := by
    simpa [prefixWord, tailWord_1642489, baseEnd_1642489] using wordTrace_append hprefix tailTrace_1642489
  have hstable : (prefixWord ++ tailWord_1642489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642489).length < 2 ^ (prefixWord ++ tailWord_1642489).sum := by decide
  have hdescent : baseEnd_1642489 < baseStart_1642489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642503 : List Nat := [1, 1, 4, 3, 1, 2, 4, 1, 4]
def baseStart_1642503 : Nat := 118140960795 + 1642503 * 2 ^ 59
def prefixEnd_1642503 : Nat := 4983230072969 + 3 ^ 40 * 1642503 * 2
def baseEnd_1642503 : Nat := 374841562423063303626121

theorem tailTrace_1642503 : CollatzResearch.WordTrace tailWord_1642503 prefixEnd_1642503 374841562423063303626121 := by
  unfold tailWord_1642503
  simp only [CollatzResearch.WordTrace]
  refine ⟨59907005968499623024396163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39938003978999748682930775 59907005968499623024396163)
  ·
    refine ⟨89860508952749434536594245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59907005968499623024396163 89860508952749434536594245)
    ·
      refine ⟨16848845428640518975611421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89860508952749434536594245 16848845428640518975611421)
      ·
        refine ⟨6318317035740194615854283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16848845428640518975611421 6318317035740194615854283)
        ·
          refine ⟨9477475553610291923781425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6318317035740194615854283 9477475553610291923781425)
          ·
            refine ⟨7108106665207718942836069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9477475553610291923781425 7108106665207718942836069)
            ·
              refine ⟨1332769999726447301781763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7108106665207718942836069 1332769999726447301781763)
              ·
                refine ⟨1999154999589670952672645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1332769999726447301781763 1999154999589670952672645)
                ·
                  refine ⟨374841562423063303626121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1999154999589670952672645 374841562423063303626121)
                  ·
                    rfl

theorem cell21_1642503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 4].length) (baseStart_1642503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1642503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1642503 prefixEnd_1642503 := by exact prefixLift 1642503
  have htrace : WordTrace (prefixWord ++ tailWord_1642503) baseStart_1642503 baseEnd_1642503 := by
    simpa [prefixWord, tailWord_1642503, baseEnd_1642503] using wordTrace_append hprefix tailTrace_1642503
  have hstable : (prefixWord ++ tailWord_1642503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642503).length < 2 ^ (prefixWord ++ tailWord_1642503).sum := by decide
  have hdescent : baseEnd_1642503 < baseStart_1642503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642582 : List Nat := [5, 2, 2, 1, 1, 1, 1, 5, 3]
def baseStart_1642582 : Nat := 118140960795 + 1642582 * 2 ^ 59
def prefixEnd_1642582 : Nat := 4983230072969 + 3 ^ 40 * 1642582 * 2
def baseEnd_1642582 : Nat := 374859591299376721809293

theorem tailTrace_1642582 : CollatzResearch.WordTrace tailWord_1642582 prefixEnd_1642582 374859591299376721809293 := by
  unfold tailWord_1642582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3744367958450838719782625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39939924890142279677681333 3744367958450838719782625)
  ·
    refine ⟨2808275968838129039836969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3744367958450838719782625 2808275968838129039836969)
    ·
      refine ⟨2106206976628596779877727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2808275968838129039836969 2106206976628596779877727)
      ·
        refine ⟨3159310464942895169816591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2106206976628596779877727 3159310464942895169816591)
        ·
          refine ⟨4738965697414342754724887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3159310464942895169816591 4738965697414342754724887)
          ·
            refine ⟨7108448546121514132087331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4738965697414342754724887 7108448546121514132087331)
            ·
              refine ⟨10662672819182271198130997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7108448546121514132087331 10662672819182271198130997)
              ·
                refine ⟨999625576798337924824781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10662672819182271198130997 999625576798337924824781)
                ·
                  refine ⟨374859591299376721809293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 999625576798337924824781 374859591299376721809293)
                  ·
                    rfl

theorem cell21_1642582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_1642582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1642582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1642582 prefixEnd_1642582 := by exact prefixLift 1642582
  have htrace : WordTrace (prefixWord ++ tailWord_1642582) baseStart_1642582 baseEnd_1642582 := by
    simpa [prefixWord, tailWord_1642582, baseEnd_1642582] using wordTrace_append hprefix tailTrace_1642582
  have hstable : (prefixWord ++ tailWord_1642582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642582).length < 2 ^ (prefixWord ++ tailWord_1642582).sum := by decide
  have hdescent : baseEnd_1642582 < baseStart_1642582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642607 : List Nat := [1, 1, 2, 1, 3, 5, 2, 1, 5]
def baseStart_1642607 : Nat := 118140960795 + 1642607 * 2 ^ 59
def prefixEnd_1642607 : Nat := 4983230072969 + 3 ^ 40 * 1642607 * 2
def baseEnd_1642607 : Nat := 374865296639982233892575

theorem tailTrace_1642607 : CollatzResearch.WordTrace tailWord_1642607 prefixEnd_1642607 374865296639982233892575 := by
  unfold tailWord_1642607
  simp only [CollatzResearch.WordTrace]
  refine ⟨59910799160122848786182075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39940532773415232524121383 59910799160122848786182075)
  ·
    refine ⟨89866198740184273179273113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59910799160122848786182075 89866198740184273179273113)
    ·
      refine ⟨67399649055138204884454835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89866198740184273179273113 67399649055138204884454835)
      ·
        refine ⟨101099473582707307326682253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67399649055138204884454835 101099473582707307326682253)
        ·
          refine ⟨37912302593515240247505845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101099473582707307326682253 37912302593515240247505845)
          ·
            refine ⟨3554278368142053773203673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37912302593515240247505845 3554278368142053773203673)
            ·
              refine ⟨2665708776106540329902755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3554278368142053773203673 2665708776106540329902755)
              ·
                refine ⟨3998563164159810494854133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2665708776106540329902755 3998563164159810494854133)
                ·
                  refine ⟨374865296639982233892575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3998563164159810494854133 374865296639982233892575)
                  ·
                    rfl

theorem cell21_1642607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 5].length) (baseStart_1642607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1642607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1642607 prefixEnd_1642607 := by exact prefixLift 1642607
  have htrace : WordTrace (prefixWord ++ tailWord_1642607) baseStart_1642607 baseEnd_1642607 := by
    simpa [prefixWord, tailWord_1642607, baseEnd_1642607] using wordTrace_append hprefix tailTrace_1642607
  have hstable : (prefixWord ++ tailWord_1642607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642607).length < 2 ^ (prefixWord ++ tailWord_1642607).sum := by decide
  have hdescent : baseEnd_1642607 < baseStart_1642607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642658 : List Nat := [3, 3, 1, 3, 1, 2, 3, 2, 3]
def baseStart_1642658 : Nat := 118140960795 + 1642658 * 2 ^ 59
def prefixEnd_1642658 : Nat := 4983230072969 + 3 ^ 40 * 1642658 * 2
def baseEnd_1642658 : Nat := 374876935534817478542471

theorem tailTrace_1642658 : CollatzResearch.WordTrace tailWord_1642658 prefixEnd_1642658 374876935534817478542471 := by
  unfold tailWord_1642658
  simp only [CollatzResearch.WordTrace]
  refine ⟨14978164820734521124072157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39941772855292056330859085 14978164820734521124072157)
  ·
    refine ⟨5616811807775445421527059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14978164820734521124072157 5616811807775445421527059)
    ·
      refine ⟨8425217711663168132290589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5616811807775445421527059 8425217711663168132290589)
      ·
        refine ⟨3159456641873688049608971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8425217711663168132290589 3159456641873688049608971)
        ·
          refine ⟨4739184962810532074413457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3159456641873688049608971 4739184962810532074413457)
          ·
            refine ⟨3554388722107899055810093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4739184962810532074413457 3554388722107899055810093)
            ·
              refine ⟨1332895770790462145928785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3554388722107899055810093 1332895770790462145928785)
              ·
                refine ⟨999671828092846609446589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1332895770790462145928785 999671828092846609446589)
                ·
                  refine ⟨374876935534817478542471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 999671828092846609446589 374876935534817478542471)
                  ·
                    rfl

theorem cell21_1642658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_1642658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1642658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1642658 prefixEnd_1642658 := by exact prefixLift 1642658
  have htrace : WordTrace (prefixWord ++ tailWord_1642658) baseStart_1642658 baseEnd_1642658 := by
    simpa [prefixWord, tailWord_1642658, baseEnd_1642658] using wordTrace_append hprefix tailTrace_1642658
  have hstable : (prefixWord ++ tailWord_1642658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642658).length < 2 ^ (prefixWord ++ tailWord_1642658).sum := by decide
  have hdescent : baseEnd_1642658 < baseStart_1642658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642669 : List Nat := [1, 5, 2, 1, 2, 2, 2, 6]
def baseStart_1642669 : Nat := 118140960795 + 1642669 * 2 ^ 59
def prefixEnd_1642669 : Nat := 4983230072969 + 3 ^ 40 * 1642669 * 2
def baseEnd_1642669 : Nat := 124959815294894634619705

theorem tailTrace_1642669 : CollatzResearch.WordTrace tailWord_1642669 prefixEnd_1642669 124959815294894634619705 := by
  unfold tailWord_1642669
  simp only [CollatzResearch.WordTrace]
  refine ⟨59913060485898233374939061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39942040323932155583292707 59913060485898233374939061)
  ·
    refine ⟨5616849420552959378900537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59913060485898233374939061 5616849420552959378900537)
    ·
      refine ⟨4212637065414719534175403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5616849420552959378900537 4212637065414719534175403)
      ·
        refine ⟨6318955598122079301263105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4212637065414719534175403 6318955598122079301263105)
        ·
          refine ⟨4739216698591559475947329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6318955598122079301263105 4739216698591559475947329)
          ·
            refine ⟨3554412523943669606960497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4739216698591559475947329 3554412523943669606960497)
            ·
              refine ⟨2665809392957752205220373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3554412523943669606960497 2665809392957752205220373)
              ·
                refine ⟨124959815294894634619705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2665809392957752205220373 124959815294894634619705)
                ·
                  rfl

theorem cell21_1642669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 6].length) (baseStart_1642669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1642669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1642669 prefixEnd_1642669 := by exact prefixLift 1642669
  have htrace : WordTrace (prefixWord ++ tailWord_1642669) baseStart_1642669 baseEnd_1642669 := by
    simpa [prefixWord, tailWord_1642669, baseEnd_1642669] using wordTrace_append hprefix tailTrace_1642669
  have hstable : (prefixWord ++ tailWord_1642669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642669).length < 2 ^ (prefixWord ++ tailWord_1642669).sum := by decide
  have hdescent : baseEnd_1642669 < baseStart_1642669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642717 : List Nat := [1, 4, 3, 2, 1, 2, 1, 4, 3]
def baseStart_1642717 : Nat := 118140960795 + 1642717 * 2 ^ 59
def prefixEnd_1642717 : Nat := 4983230072969 + 3 ^ 40 * 1642717 * 2
def baseEnd_1642717 : Nat := 374890400138646487059017

theorem tailTrace_1642717 : CollatzResearch.WordTrace tailWord_1642717 prefixEnd_1642717 374890400138646487059017 := by
  unfold tailWord_1642717
  simp only [CollatzResearch.WordTrace]
  refine ⟨59914811189724337572686405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39943207459816225048457603 59914811189724337572686405)
  ·
    refine ⟨11234027098073313294878701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59914811189724337572686405 11234027098073313294878701)
    ·
      refine ⟨4212760161777492485579513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11234027098073313294878701 4212760161777492485579513)
      ·
        refine ⟨3159570121333119364184635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4212760161777492485579513 3159570121333119364184635)
        ·
          refine ⟨4739355181999679046276953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3159570121333119364184635 4739355181999679046276953)
          ·
            refine ⟨3554516386499759284707715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4739355181999679046276953 3554516386499759284707715)
            ·
              refine ⟨5331774579749638927061573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3554516386499759284707715 5331774579749638927061573)
              ·
                refine ⟨999707733703057298824045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5331774579749638927061573 999707733703057298824045)
                ·
                  refine ⟨374890400138646487059017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 999707733703057298824045 374890400138646487059017)
                  ·
                    rfl

theorem cell21_1642717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_1642717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1642717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1642717 prefixEnd_1642717 := by exact prefixLift 1642717
  have htrace : WordTrace (prefixWord ++ tailWord_1642717) baseStart_1642717 baseEnd_1642717 := by
    simpa [prefixWord, tailWord_1642717, baseEnd_1642717] using wordTrace_append hprefix tailTrace_1642717
  have hstable : (prefixWord ++ tailWord_1642717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642717).length < 2 ^ (prefixWord ++ tailWord_1642717).sum := by decide
  have hdescent : baseEnd_1642717 < baseStart_1642717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642728 : List Nat := [2, 1, 4, 1, 2, 2, 3, 6]
def baseStart_1642728 : Nat := 118140960795 + 1642728 * 2 ^ 59
def prefixEnd_1642728 : Nat := 4983230072969 + 3 ^ 40 * 1642728 * 2
def baseEnd_1642728 : Nat := 124964303496170970791887

theorem tailTrace_1642728 : CollatzResearch.WordTrace tailWord_1642728 prefixEnd_1642728 124964303496170970791887 := by
  unfold tailWord_1642728
  simp only [CollatzResearch.WordTrace]
  refine ⟨29957606196342243225668419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39943474928456324300891225 29957606196342243225668419)
  ·
    refine ⟨44936409294513364838502629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29957606196342243225668419 44936409294513364838502629)
    ·
      refine ⟨8425576742721255907219243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44936409294513364838502629 8425576742721255907219243)
      ·
        refine ⟨12638365114081883860828865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8425576742721255907219243 12638365114081883860828865)
        ·
          refine ⟨9478773835561412895621649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12638365114081883860828865 9478773835561412895621649)
          ·
            refine ⟨7109080376671059671716237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9478773835561412895621649 7109080376671059671716237)
            ·
              refine ⟨2665905141251647376893589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7109080376671059671716237 2665905141251647376893589)
              ·
                refine ⟨124964303496170970791887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2665905141251647376893589 124964303496170970791887)
                ·
                  rfl

theorem cell21_1642728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 6].length) (baseStart_1642728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1642728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1642728 prefixEnd_1642728 := by exact prefixLift 1642728
  have htrace : WordTrace (prefixWord ++ tailWord_1642728) baseStart_1642728 baseEnd_1642728 := by
    simpa [prefixWord, tailWord_1642728, baseEnd_1642728] using wordTrace_append hprefix tailTrace_1642728
  have hstable : (prefixWord ++ tailWord_1642728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642728).length < 2 ^ (prefixWord ++ tailWord_1642728).sum := by decide
  have hdescent : baseEnd_1642728 < baseStart_1642728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642787 : List Nat := [1, 1, 1, 4, 2, 2, 2, 8]
def baseStart_1642787 : Nat := 118140960795 + 1642787 * 2 ^ 59
def prefixEnd_1642787 : Nat := 4983230072969 + 3 ^ 40 * 1642787 * 2
def baseEnd_1642787 : Nat := 124968791697447306964069

theorem tailTrace_1642787 : CollatzResearch.WordTrace tailWord_1642787 prefixEnd_1642787 124968791697447306964069 := by
  unfold tailWord_1642787
  simp only [CollatzResearch.WordTrace]
  refine ⟨59917364299470739527734615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39944909532980493018489743 59917364299470739527734615)
  ·
    refine ⟨89876046449206109291601923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59917364299470739527734615 89876046449206109291601923)
    ·
      refine ⟨134814069673809163937402885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89876046449206109291601923 134814069673809163937402885)
      ·
        refine ⟨25277638063839218238263041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134814069673809163937402885 25277638063839218238263041)
        ·
          refine ⟨18958228547879413678697281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25277638063839218238263041 18958228547879413678697281)
          ·
            refine ⟨14218671410909560259022961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18958228547879413678697281 14218671410909560259022961)
            ·
              refine ⟨10664003558182170194267221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14218671410909560259022961 10664003558182170194267221)
              ·
                refine ⟨124968791697447306964069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10664003558182170194267221 124968791697447306964069)
                ·
                  rfl

theorem cell21_1642787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 8].length) (baseStart_1642787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1642787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1642787 prefixEnd_1642787 := by exact prefixLift 1642787
  have htrace : WordTrace (prefixWord ++ tailWord_1642787) baseStart_1642787 baseEnd_1642787 := by
    simpa [prefixWord, tailWord_1642787, baseEnd_1642787] using wordTrace_append hprefix tailTrace_1642787
  have hstable : (prefixWord ++ tailWord_1642787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642787).length < 2 ^ (prefixWord ++ tailWord_1642787).sum := by decide
  have hdescent : baseEnd_1642787 < baseStart_1642787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642942 : List Nat := [4, 2, 1, 1, 1, 1, 5, 2, 4]
def baseStart_1642942 : Nat := 118140960795 + 1642942 * 2 ^ 59
def prefixEnd_1642942 : Nat := 4983230072969 + 3 ^ 40 * 1642942 * 2
def baseEnd_1642942 : Nat := 374941748204096095808557

theorem tailTrace_1642942 : CollatzResearch.WordTrace tailWord_1642942 prefixEnd_1642942 374941748204096095808557 := by
  unfold tailWord_1642942
  simp only [CollatzResearch.WordTrace]
  refine ⟨7490377201738650124953385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39948678409272800666418053 7490377201738650124953385)
  ·
    refine ⟨5617782901303987593715039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7490377201738650124953385 5617782901303987593715039)
    ·
      refine ⟨8426674351955981390572559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5617782901303987593715039 8426674351955981390572559)
      ·
        refine ⟨12640011527933972085858839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8426674351955981390572559 12640011527933972085858839)
        ·
          refine ⟨18960017291900958128788259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12640011527933972085858839 18960017291900958128788259)
          ·
            refine ⟨28440025937851437193182389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18960017291900958128788259 28440025937851437193182389)
            ·
              refine ⟨2666252431673572236860849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28440025937851437193182389 2666252431673572236860849)
              ·
                refine ⟨1999689323755179177645637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2666252431673572236860849 1999689323755179177645637)
                ·
                  refine ⟨374941748204096095808557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1999689323755179177645637 374941748204096095808557)
                  ·
                    rfl

theorem cell21_1642942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_1642942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1642942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1642942 prefixEnd_1642942 := by exact prefixLift 1642942
  have htrace : WordTrace (prefixWord ++ tailWord_1642942) baseStart_1642942 baseEnd_1642942 := by
    simpa [prefixWord, tailWord_1642942, baseEnd_1642942] using wordTrace_append hprefix tailTrace_1642942
  have hstable : (prefixWord ++ tailWord_1642942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642942).length < 2 ^ (prefixWord ++ tailWord_1642942).sum := by decide
  have hdescent : baseEnd_1642942 < baseStart_1642942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642970 : List Nat := [3, 1, 1, 2, 3, 1, 1, 4, 5]
def baseStart_1642970 : Nat := 118140960795 + 1642970 * 2 ^ 59
def prefixEnd_1642970 : Nat := 4983230072969 + 3 ^ 40 * 1642970 * 2
def baseEnd_1642970 : Nat := 374948138185574269341833

theorem tailTrace_1642970 : CollatzResearch.WordTrace tailWord_1642970 prefixEnd_1642970 374948138185574269341833 := by
  unfold tailWord_1642970
  simp only [CollatzResearch.WordTrace]
  refine ⟨14981009714451940445411591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39949359238538507854430909 14981009714451940445411591)
  ·
    refine ⟨22471514571677910668117387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14981009714451940445411591 22471514571677910668117387)
    ·
      refine ⟨33707271857516866002176081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22471514571677910668117387 33707271857516866002176081)
      ·
        refine ⟨25280453893137649501632061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33707271857516866002176081 25280453893137649501632061)
        ·
          refine ⟨9480170209926618563112023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25280453893137649501632061 9480170209926618563112023)
          ·
            refine ⟨14220255314889927844668035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9480170209926618563112023 14220255314889927844668035)
            ·
              refine ⟨21330382972334891767002053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14220255314889927844668035 21330382972334891767002053)
              ·
                refine ⟨3999446807312792206312885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21330382972334891767002053 3999446807312792206312885)
                ·
                  refine ⟨374948138185574269341833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3999446807312792206312885 374948138185574269341833)
                  ·
                    rfl

theorem cell21_1642970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_1642970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1642970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1642970 prefixEnd_1642970 := by exact prefixLift 1642970
  have htrace : WordTrace (prefixWord ++ tailWord_1642970) baseStart_1642970 baseEnd_1642970 := by
    simpa [prefixWord, tailWord_1642970, baseEnd_1642970] using wordTrace_append hprefix tailTrace_1642970
  have hstable : (prefixWord ++ tailWord_1642970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642970).length < 2 ^ (prefixWord ++ tailWord_1642970).sum := by decide
  have hdescent : baseEnd_1642970 < baseStart_1642970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643063 : List Nat := [1, 1, 3, 1, 2, 3, 3, 4, 3]
def baseStart_1643063 : Nat := 118140960795 + 1643063 * 2 ^ 59
def prefixEnd_1643063 : Nat := 4983230072969 + 3 ^ 40 * 1643063 * 2
def baseEnd_1643063 : Nat := 374969362052626774291643

theorem tailTrace_1643063 : CollatzResearch.WordTrace tailWord_1643063 prefixEnd_1643063 374969362052626774291643 := by
  unfold tailWord_1643063
  simp only [CollatzResearch.WordTrace]
  refine ⟨59927430846470838664781843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39951620564313892443187895 59927430846470838664781843)
  ·
    refine ⟨89891146269706257997172765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59927430846470838664781843 89891146269706257997172765)
    ·
      refine ⟨33709179851139846748939787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89891146269706257997172765 33709179851139846748939787)
      ·
        refine ⟨50563769776709770123409681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33709179851139846748939787 50563769776709770123409681)
        ·
          refine ⟨37922827332532327592557261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50563769776709770123409681 37922827332532327592557261)
          ·
            refine ⟨14221060249699622847208973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37922827332532327592557261 14221060249699622847208973)
            ·
              refine ⟨5332897593637358567703365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14221060249699622847208973 5332897593637358567703365)
              ·
                refine ⟨999918298807004731444381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5332897593637358567703365 999918298807004731444381)
                ·
                  refine ⟨374969362052626774291643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 999918298807004731444381 374969362052626774291643)
                  ·
                    rfl

theorem cell21_1643063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4, 3].length) (baseStart_1643063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1643063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1643063 prefixEnd_1643063 := by exact prefixLift 1643063
  have htrace : WordTrace (prefixWord ++ tailWord_1643063) baseStart_1643063 baseEnd_1643063 := by
    simpa [prefixWord, tailWord_1643063, baseEnd_1643063] using wordTrace_append hprefix tailTrace_1643063
  have hstable : (prefixWord ++ tailWord_1643063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643063).length < 2 ^ (prefixWord ++ tailWord_1643063).sum := by decide
  have hdescent : baseEnd_1643063 < baseStart_1643063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643077 : List Nat := [1, 3, 1, 1, 1, 5, 2, 3, 4]
def baseStart_1643077 : Nat := 118140960795 + 1643077 * 2 ^ 59
def prefixEnd_1643077 : Nat := 4983230072969 + 3 ^ 40 * 1643077 * 2
def baseEnd_1643077 : Nat := 374972557043365861058281

theorem tailTrace_1643077 : CollatzResearch.WordTrace tailWord_1643077 prefixEnd_1643077 374972557043365861058281 := by
  unfold tailWord_1643077
  simp only [CollatzResearch.WordTrace]
  refine ⟨59927941468420119055791485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39951960978946746037194323 59927941468420119055791485)
  ·
    refine ⟨22472978050657544645921807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59927941468420119055791485 22472978050657544645921807)
    ·
      refine ⟨33709467075986316968882711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22472978050657544645921807 33709467075986316968882711)
      ·
        refine ⟨50564200613979475453324067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33709467075986316968882711 50564200613979475453324067)
        ·
          refine ⟨75846300920969213179986101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50564200613979475453324067 75846300920969213179986101)
          ·
            refine ⟨7110590711340863735623697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75846300920969213179986101 7110590711340863735623697)
            ·
              refine ⟨5332943033505647801717773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7110590711340863735623697 5332943033505647801717773)
              ·
                refine ⟨1999853637564617925644165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5332943033505647801717773 1999853637564617925644165)
                ·
                  refine ⟨374972557043365861058281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1999853637564617925644165 374972557043365861058281)
                  ·
                    rfl

theorem cell21_1643077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_1643077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1643077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1643077 prefixEnd_1643077 := by exact prefixLift 1643077
  have htrace : WordTrace (prefixWord ++ tailWord_1643077) baseStart_1643077 baseEnd_1643077 := by
    simpa [prefixWord, tailWord_1643077, baseEnd_1643077] using wordTrace_append hprefix tailTrace_1643077
  have hstable : (prefixWord ++ tailWord_1643077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643077).length < 2 ^ (prefixWord ++ tailWord_1643077).sum := by decide
  have hdescent : baseEnd_1643077 < baseStart_1643077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643198 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 7]
def baseStart_1643198 : Nat := 118140960795 + 1643198 * 2 ^ 59
def prefixEnd_1643198 : Nat := 4983230072969 + 3 ^ 40 * 1643198 * 2
def baseEnd_1643198 : Nat := 375000170891896539541367

theorem tailTrace_1643198 : CollatzResearch.WordTrace tailWord_1643198 prefixEnd_1643198 375000170891896539541367 := by
  unfold tailWord_1643198
  simp only [CollatzResearch.WordTrace]
  refine ⟨7491544337622719590118281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39954903133987837813964165 7491544337622719590118281)
  ·
    refine ⟨5618658253217039692588711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7491544337622719590118281 5618658253217039692588711)
    ·
      refine ⟨8427987379825559538883067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5618658253217039692588711 8427987379825559538883067)
      ·
        refine ⟨12641981069738339308324601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8427987379825559538883067 12641981069738339308324601)
        ·
          refine ⟨9481485802303754481243451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12641981069738339308324601 9481485802303754481243451)
          ·
            refine ⟨14222228703455631721865177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9481485802303754481243451 14222228703455631721865177)
            ·
              refine ⟨10666671527591723791398883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14222228703455631721865177 10666671527591723791398883)
              ·
                refine ⟨16000007291387585687098325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10666671527591723791398883 16000007291387585687098325)
                ·
                  refine ⟨375000170891896539541367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16000007291387585687098325 375000170891896539541367)
                  ·
                    rfl

theorem cell21_1643198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_1643198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1643198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1643198 prefixEnd_1643198 := by exact prefixLift 1643198
  have htrace : WordTrace (prefixWord ++ tailWord_1643198) baseStart_1643198 baseEnd_1643198 := by
    simpa [prefixWord, tailWord_1643198, baseEnd_1643198] using wordTrace_append hprefix tailTrace_1643198
  have hstable : (prefixWord ++ tailWord_1643198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643198).length < 2 ^ (prefixWord ++ tailWord_1643198).sum := by decide
  have hdescent : baseEnd_1643198 < baseStart_1643198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643260 : List Nat := [2, 2, 2, 1, 3, 3, 3, 5]
def baseStart_1643260 : Nat := 118140960795 + 1643260 * 2 ^ 59
def prefixEnd_1643260 : Nat := 4983230072969 + 3 ^ 40 * 1643260 * 2
def baseEnd_1643260 : Nat := 125004773378866069835969

theorem tailTrace_1643260 : CollatzResearch.WordTrace tailWord_1643260 prefixEnd_1643260 125004773378866069835969 := by
  unfold tailWord_1643260
  simp only [CollatzResearch.WordTrace]
  refine ⟨29967308013378570654851617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39956410684504760873135489 29967308013378570654851617)
  ·
    refine ⟨22475481010033927991138713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29967308013378570654851617 22475481010033927991138713)
    ·
      refine ⟨16856610757525445993354035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22475481010033927991138713 16856610757525445993354035)
      ·
        refine ⟨25284916136288168990031053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16856610757525445993354035 25284916136288168990031053)
        ·
          refine ⟨9481843551108063371261645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25284916136288168990031053 9481843551108063371261645)
          ·
            refine ⟨3555691331665523764223117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9481843551108063371261645 3555691331665523764223117)
            ·
              refine ⟨1333384249374571411583669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3555691331665523764223117 1333384249374571411583669)
              ·
                refine ⟨125004773378866069835969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1333384249374571411583669 125004773378866069835969)
                ·
                  rfl

theorem cell21_1643260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 5].length) (baseStart_1643260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1643260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1643260 prefixEnd_1643260 := by exact prefixLift 1643260
  have htrace : WordTrace (prefixWord ++ tailWord_1643260) baseStart_1643260 baseEnd_1643260 := by
    simpa [prefixWord, tailWord_1643260, baseEnd_1643260] using wordTrace_append hprefix tailTrace_1643260
  have hstable : (prefixWord ++ tailWord_1643260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643260).length < 2 ^ (prefixWord ++ tailWord_1643260).sum := by decide
  have hdescent : baseEnd_1643260 < baseStart_1643260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643325 : List Nat := [1, 4, 1, 4, 2, 2, 1, 3, 3]
def baseStart_1643325 : Nat := 118140960795 + 1643325 * 2 ^ 59
def prefixEnd_1643325 : Nat := 4983230072969 + 3 ^ 40 * 1643325 * 2
def baseEnd_1643325 : Nat := 375029154022172540924441

theorem tailTrace_1643325 : CollatzResearch.WordTrace tailWord_1643325 prefixEnd_1643325 375029154022172540924441 := by
  unfold tailWord_1643325
  simp only [CollatzResearch.WordTrace]
  refine ⟨59936986771521657410819429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39957991181014438273879619 59936986771521657410819429)
  ·
    refine ⟨11238185019660310764528643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59936986771521657410819429 11238185019660310764528643)
    ·
      refine ⟨16857277529490466146792965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11238185019660310764528643 16857277529490466146792965)
      ·
        refine ⟨3160739536779462402523681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16857277529490466146792965 3160739536779462402523681)
        ·
          refine ⟨2370554652584596801892761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3160739536779462402523681 2370554652584596801892761)
          ·
            refine ⟨1777915989438447601419571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2370554652584596801892761 1777915989438447601419571)
            ·
              refine ⟨2666873984157671402129357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1777915989438447601419571 2666873984157671402129357)
              ·
                refine ⟨1000077744059126775798509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2666873984157671402129357 1000077744059126775798509)
                ·
                  refine ⟨375029154022172540924441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1000077744059126775798509 375029154022172540924441)
                  ·
                    rfl

theorem cell21_1643325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_1643325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1643325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1643325 prefixEnd_1643325 := by exact prefixLift 1643325
  have htrace : WordTrace (prefixWord ++ tailWord_1643325) baseStart_1643325 baseEnd_1643325 := by
    simpa [prefixWord, tailWord_1643325, baseEnd_1643325] using wordTrace_append hprefix tailTrace_1643325
  have hstable : (prefixWord ++ tailWord_1643325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643325).length < 2 ^ (prefixWord ++ tailWord_1643325).sum := by decide
  have hdescent : baseEnd_1643325 < baseStart_1643325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643409 : List Nat := [1, 2, 2, 1, 1, 1, 3, 5, 5]
def baseStart_1643409 : Nat := 118140960795 + 1643409 * 2 ^ 59
def prefixEnd_1643409 : Nat := 4983230072969 + 3 ^ 40 * 1643409 * 2
def baseEnd_1643409 : Nat := 375048323966607061524269

theorem tailTrace_1643409 : CollatzResearch.WordTrace tailWord_1643409 prefixEnd_1643409 375048323966607061524269 := by
  unfold tailWord_1643409
  simp only [CollatzResearch.WordTrace]
  refine ⟨59940050503217339756877281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39960033668811559837918187 59940050503217339756877281)
  ·
    refine ⟨44955037877413004817657961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59940050503217339756877281 44955037877413004817657961)
    ·
      refine ⟨33716278408059753613243471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44955037877413004817657961 33716278408059753613243471)
      ·
        refine ⟨50574417612089630419865207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33716278408059753613243471 50574417612089630419865207)
        ·
          refine ⟨75861626418134445629797811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50574417612089630419865207 75861626418134445629797811)
          ·
            refine ⟨113792439627201668444696717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75861626418134445629797811 113792439627201668444696717)
            ·
              refine ⟨42672164860200625666761269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113792439627201668444696717 42672164860200625666761269)
              ·
                refine ⟨4000515455643808656258869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42672164860200625666761269 4000515455643808656258869)
                ·
                  refine ⟨375048323966607061524269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4000515455643808656258869 375048323966607061524269)
                  ·
                    rfl

theorem cell21_1643409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 5].length) (baseStart_1643409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1643409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1643409 prefixEnd_1643409 := by exact prefixLift 1643409
  have htrace : WordTrace (prefixWord ++ tailWord_1643409) baseStart_1643409 baseEnd_1643409 := by
    simpa [prefixWord, tailWord_1643409, baseEnd_1643409] using wordTrace_append hprefix tailTrace_1643409
  have hstable : (prefixWord ++ tailWord_1643409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643409).length < 2 ^ (prefixWord ++ tailWord_1643409).sum := by decide
  have hdescent : baseEnd_1643409 < baseStart_1643409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643426 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 7]
def baseStart_1643426 : Nat := 118140960795 + 1643426 * 2 ^ 59
def prefixEnd_1643426 : Nat := 4983230072969 + 3 ^ 40 * 1643426 * 2
def baseEnd_1643426 : Nat := 375052203598218809740901

theorem tailTrace_1643426 : CollatzResearch.WordTrace tailWord_1643426 prefixEnd_1643426 375052203598218809740901 := by
  unfold tailWord_1643426
  simp only [CollatzResearch.WordTrace]
  refine ⟨14985167636038937915061533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39960447029437167773497421 14985167636038937915061533)
  ·
    refine ⟨5619437863514601718148075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14985167636038937915061533 5619437863514601718148075)
    ·
      refine ⟨8429156795271902577222113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5619437863514601718148075 8429156795271902577222113)
      ·
        refine ⟨6321867596453926932916585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8429156795271902577222113 6321867596453926932916585)
        ·
          refine ⟨4741400697340445199687439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6321867596453926932916585 4741400697340445199687439)
          ·
            refine ⟨7112101046010667799531159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4741400697340445199687439 7112101046010667799531159)
            ·
              refine ⟨10668151569016001699296739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7112101046010667799531159 10668151569016001699296739)
              ·
                refine ⟨16002227353524002548945109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10668151569016001699296739 16002227353524002548945109)
                ·
                  refine ⟨375052203598218809740901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16002227353524002548945109 375052203598218809740901)
                  ·
                    rfl

theorem cell21_1643426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_1643426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1643426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1643426 prefixEnd_1643426 := by exact prefixLift 1643426
  have htrace : WordTrace (prefixWord ++ tailWord_1643426) baseStart_1643426 baseEnd_1643426 := by
    simpa [prefixWord, tailWord_1643426, baseEnd_1643426] using wordTrace_append hprefix tailTrace_1643426
  have hstable : (prefixWord ++ tailWord_1643426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643426).length < 2 ^ (prefixWord ++ tailWord_1643426).sum := by decide
  have hdescent : baseEnd_1643426 < baseStart_1643426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643446 : List Nat := [5, 1, 4, 1, 1, 1, 8]
def baseStart_1643446 : Nat := 118140960795 + 1643446 * 2 ^ 59
def prefixEnd_1643446 : Nat := 4983230072969 + 3 ^ 40 * 1643446 * 2
def baseEnd_1643446 : Nat := 41672974207855913267503

theorem tailTrace_1643446 : CollatzResearch.WordTrace tailWord_1643446 prefixEnd_1643446 41672974207855913267503 := by
  unfold tailWord_1643446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3746337500255205942248387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39960933336055530050649461 3746337500255205942248387)
  ·
    refine ⟨5619506250382808913372581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3746337500255205942248387 5619506250382808913372581)
    ·
      refine ⟨1053657421946776671257359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5619506250382808913372581 1053657421946776671257359)
      ·
        refine ⟨1580486132920165006886039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1053657421946776671257359 1580486132920165006886039)
        ·
          refine ⟨2370729199380247510329059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1580486132920165006886039 2370729199380247510329059)
          ·
            refine ⟨3556093799070371265493589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2370729199380247510329059 3556093799070371265493589)
            ·
              refine ⟨41672974207855913267503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3556093799070371265493589 41672974207855913267503)
              ·
                rfl

theorem cell21_1643446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 8].length) (baseStart_1643446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1643446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1643446 prefixEnd_1643446 := by exact prefixLift 1643446
  have htrace : WordTrace (prefixWord ++ tailWord_1643446) baseStart_1643446 baseEnd_1643446 := by
    simpa [prefixWord, tailWord_1643446, baseEnd_1643446] using wordTrace_append hprefix tailTrace_1643446
  have hstable : (prefixWord ++ tailWord_1643446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643446).length < 2 ^ (prefixWord ++ tailWord_1643446).sum := by decide
  have hdescent : baseEnd_1643446 < baseStart_1643446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643460 : List Nat := [2, 3, 3, 3, 1, 1, 2, 1, 5]
def baseStart_1643460 : Nat := 118140960795 + 1643460 * 2 ^ 59
def prefixEnd_1643460 : Nat := 4983230072969 + 3 ^ 40 * 1643460 * 2
def baseEnd_1643460 : Nat := 375059962861442306174165

theorem tailTrace_1643460 : CollatzResearch.WordTrace tailWord_1643460 prefixEnd_1643460 375059962861442306174165 := by
  unfold tailWord_1643460
  simp only [CollatzResearch.WordTrace]
  refine ⟨29970955313016287733491917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39961273750688383644655889 29970955313016287733491917)
  ·
    refine ⟨11239108242381107900059469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29970955313016287733491917 11239108242381107900059469)
    ·
      refine ⟨4214665590892915462522301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11239108242381107900059469 4214665590892915462522301)
      ·
        refine ⟨1580499596584843298445863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4214665590892915462522301 1580499596584843298445863)
        ·
          refine ⟨2370749394877264947668795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1580499596584843298445863 2370749394877264947668795)
          ·
            refine ⟨3556124092315897421503193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2370749394877264947668795 3556124092315897421503193)
            ·
              refine ⟨2667093069236923066127395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3556124092315897421503193 2667093069236923066127395)
              ·
                refine ⟨4000639603855384599191093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2667093069236923066127395 4000639603855384599191093)
                ·
                  refine ⟨375059962861442306174165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4000639603855384599191093 375059962861442306174165)
                  ·
                    rfl

theorem cell21_1643460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_1643460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1643460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1643460 prefixEnd_1643460 := by exact prefixLift 1643460
  have htrace : WordTrace (prefixWord ++ tailWord_1643460) baseStart_1643460 baseEnd_1643460 := by
    simpa [prefixWord, tailWord_1643460, baseEnd_1643460] using wordTrace_append hprefix tailTrace_1643460
  have hstable : (prefixWord ++ tailWord_1643460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643460).length < 2 ^ (prefixWord ++ tailWord_1643460).sum := by decide
  have hdescent : baseEnd_1643460 < baseStart_1643460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643516 : List Nat := [2, 2, 2, 1, 2, 3, 2, 1, 6]
def baseStart_1643516 : Nat := 118140960795 + 1643516 * 2 ^ 59
def prefixEnd_1643516 : Nat := 4983230072969 + 3 ^ 40 * 1643516 * 2
def baseEnd_1643516 : Nat := 375072742824398653240717

theorem tailTrace_1643516 : CollatzResearch.WordTrace tailWord_1643516 prefixEnd_1643516 375072742824398653240717 := by
  unfold tailWord_1643516
  simp only [CollatzResearch.WordTrace]
  refine ⟨29971976556914848515511201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39962635409219798020681601 29971976556914848515511201)
  ·
    refine ⟨22478982417686136386633401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29971976556914848515511201 22478982417686136386633401)
    ·
      refine ⟨16859236813264602289975051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22478982417686136386633401 16859236813264602289975051)
      ·
        refine ⟨25288855219896903434962577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16859236813264602289975051 25288855219896903434962577)
        ·
          refine ⟨18966641414922677576221933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25288855219896903434962577 18966641414922677576221933)
          ·
            refine ⟨7112490530596004091083225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18966641414922677576221933 7112490530596004091083225)
            ·
              refine ⟨5334367897947003068312419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7112490530596004091083225 5334367897947003068312419)
              ·
                refine ⟨8001551846920504602468629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5334367897947003068312419 8001551846920504602468629)
                ·
                  refine ⟨375072742824398653240717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8001551846920504602468629 375072742824398653240717)
                  ·
                    rfl

theorem cell21_1643516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_1643516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1643516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1643516 prefixEnd_1643516 := by exact prefixLift 1643516
  have htrace : WordTrace (prefixWord ++ tailWord_1643516) baseStart_1643516 baseEnd_1643516 := by
    simpa [prefixWord, tailWord_1643516, baseEnd_1643516] using wordTrace_append hprefix tailTrace_1643516
  have hstable : (prefixWord ++ tailWord_1643516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643516).length < 2 ^ (prefixWord ++ tailWord_1643516).sum := by decide
  have hdescent : baseEnd_1643516 < baseStart_1643516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643592 : List Nat := [2, 1, 3, 1, 1, 1, 3, 5, 4]
def baseStart_1643592 : Nat := 118140960795 + 1643592 * 2 ^ 59
def prefixEnd_1643592 : Nat := 4983230072969 + 3 ^ 40 * 1643592 * 2
def baseEnd_1643592 : Nat := 375090087059839409973895

theorem tailTrace_1643592 : CollatzResearch.WordTrace tailWord_1643592 prefixEnd_1643592 375090087059839409973895 := by
  unfold tailWord_1643592
  simp only [CollatzResearch.WordTrace]
  refine ⟨29973362530777181005394515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39964483374369574673859353 29973362530777181005394515)
  ·
    refine ⟨44960043796165771508091773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29973362530777181005394515 44960043796165771508091773)
    ·
      refine ⟨16860016423562164315534415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44960043796165771508091773 16860016423562164315534415)
      ·
        refine ⟨25290024635343246473301623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16860016423562164315534415 25290024635343246473301623)
        ·
          refine ⟨37935036953014869709952435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25290024635343246473301623 37935036953014869709952435)
          ·
            refine ⟨56902555429522304564928653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37935036953014869709952435 56902555429522304564928653)
            ·
              refine ⟨21338458286070864211848245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56902555429522304564928653 21338458286070864211848245)
              ·
                refine ⟨2000480464319143519860773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21338458286070864211848245 2000480464319143519860773)
                ·
                  refine ⟨375090087059839409973895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2000480464319143519860773 375090087059839409973895)
                  ·
                    rfl

theorem cell21_1643592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 4].length) (baseStart_1643592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1643592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1643592 prefixEnd_1643592 := by exact prefixLift 1643592
  have htrace : WordTrace (prefixWord ++ tailWord_1643592) baseStart_1643592 baseEnd_1643592 := by
    simpa [prefixWord, tailWord_1643592, baseEnd_1643592] using wordTrace_append hprefix tailTrace_1643592
  have hstable : (prefixWord ++ tailWord_1643592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643592).length < 2 ^ (prefixWord ++ tailWord_1643592).sum := by decide
  have hdescent : baseEnd_1643592 < baseStart_1643592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643626 : List Nat := [3, 1, 3, 2, 2, 3, 1, 2, 4]
def baseStart_1643626 : Nat := 118140960795 + 1643626 * 2 ^ 59
def prefixEnd_1643626 : Nat := 4983230072969 + 3 ^ 40 * 1643626 * 2
def baseEnd_1643626 : Nat := 375097846323062906407159

theorem tailTrace_1643626 : CollatzResearch.WordTrace tailWord_1643626 prefixEnd_1643626 375097846323062906407159 := by
  unfold tailWord_1643626
  simp only [CollatzResearch.WordTrace]
  refine ⟨14986991285857796454381683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39965310095620790545017821 14986991285857796454381683)
  ·
    refine ⟨22480486928786694681572525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14986991285857796454381683 22480486928786694681572525)
    ·
      refine ⟨8430182598295010505589697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22480486928786694681572525 8430182598295010505589697)
      ·
        refine ⟨6322636948721257879192273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8430182598295010505589697 6322636948721257879192273)
        ·
          refine ⟨4741977711540943409394205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6322636948721257879192273 4741977711540943409394205)
          ·
            refine ⟨1778241641827853778522827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4741977711540943409394205 1778241641827853778522827)
            ·
              refine ⟨2667362462741780667784241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1778241641827853778522827 2667362462741780667784241)
              ·
                refine ⟨2000521847056335500838181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2667362462741780667784241 2000521847056335500838181)
                ·
                  refine ⟨375097846323062906407159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2000521847056335500838181 375097846323062906407159)
                  ·
                    rfl

theorem cell21_1643626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_1643626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1643626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1643626 prefixEnd_1643626 := by exact prefixLift 1643626
  have htrace : WordTrace (prefixWord ++ tailWord_1643626) baseStart_1643626 baseEnd_1643626 := by
    simpa [prefixWord, tailWord_1643626, baseEnd_1643626] using wordTrace_append hprefix tailTrace_1643626
  have hstable : (prefixWord ++ tailWord_1643626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643626).length < 2 ^ (prefixWord ++ tailWord_1643626).sum := by decide
  have hdescent : baseEnd_1643626 < baseStart_1643626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643671 : List Nat := [1, 1, 3, 3, 3, 1, 3, 3, 3]
def baseStart_1643671 : Nat := 118140960795 + 1643671 * 2 ^ 59
def prefixEnd_1643671 : Nat := 4983230072969 + 3 ^ 40 * 1643671 * 2
def baseEnd_1643671 : Nat := 375108115936152828157067

theorem tailTrace_1643671 : CollatzResearch.WordTrace tailWord_1643671 prefixEnd_1643671 375108115936152828157067 := by
  unfold tailWord_1643671
  simp only [CollatzResearch.WordTrace]
  refine ⟨59949606428268158502914867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39966404285512105668609911 59949606428268158502914867)
  ·
    refine ⟨89924409642402237754372301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59949606428268158502914867 89924409642402237754372301)
    ·
      refine ⟨33721653615900839157889613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89924409642402237754372301 33721653615900839157889613)
      ·
        refine ⟨12645620105962814684208605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33721653615900839157889613 12645620105962814684208605)
        ·
          refine ⟨4742107539736055506578227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12645620105962814684208605 4742107539736055506578227)
          ·
            refine ⟨7113161309604083259867341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4742107539736055506578227 7113161309604083259867341)
            ·
              refine ⟨2667435491101531222450253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7113161309604083259867341 2667435491101531222450253)
              ·
                refine ⟨1000288309163074208418845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2667435491101531222450253 1000288309163074208418845)
                ·
                  refine ⟨375108115936152828157067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1000288309163074208418845 375108115936152828157067)
                  ·
                    rfl

theorem cell21_1643671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 3].length) (baseStart_1643671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1643671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1643671 prefixEnd_1643671 := by exact prefixLift 1643671
  have htrace : WordTrace (prefixWord ++ tailWord_1643671) baseStart_1643671 baseEnd_1643671 := by
    simpa [prefixWord, tailWord_1643671, baseEnd_1643671] using wordTrace_append hprefix tailTrace_1643671
  have hstable : (prefixWord ++ tailWord_1643671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643671).length < 2 ^ (prefixWord ++ tailWord_1643671).sum := by decide
  have hdescent : baseEnd_1643671 < baseStart_1643671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643727 : List Nat := [1, 1, 2, 1, 1, 3, 2, 4, 6]
def baseStart_1643727 : Nat := 118140960795 + 1643727 * 2 ^ 59
def prefixEnd_1643727 : Nat := 4983230072969 + 3 ^ 40 * 1643727 * 2
def baseEnd_1643727 : Nat := 375120895899109175223619

theorem tailTrace_1643727 : CollatzResearch.WordTrace tailWord_1643727 prefixEnd_1643727 375120895899109175223619 := by
  unfold tailWord_1643727
  simp only [CollatzResearch.WordTrace]
  refine ⟨59951648916065280066953435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39967765944043520044635623 59951648916065280066953435)
  ·
    refine ⟨89927473374097920100430153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59951648916065280066953435 89927473374097920100430153)
    ·
      refine ⟨67445605030573440075322615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89927473374097920100430153 67445605030573440075322615)
      ·
        refine ⟨101168407545860160112983923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67445605030573440075322615 101168407545860160112983923)
        ·
          refine ⟨151752611318790240169475885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101168407545860160112983923 151752611318790240169475885)
          ·
            refine ⟨56907229244546340063553457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151752611318790240169475885 56907229244546340063553457)
            ·
              refine ⟨42680421933409755047665093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56907229244546340063553457 42680421933409755047665093)
              ·
                refine ⟨8002579112514329071437205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42680421933409755047665093 8002579112514329071437205)
                ·
                  refine ⟨375120895899109175223619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8002579112514329071437205 375120895899109175223619)
                  ·
                    rfl

theorem cell21_1643727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 6].length) (baseStart_1643727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1643727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1643727 prefixEnd_1643727 := by exact prefixLift 1643727
  have htrace : WordTrace (prefixWord ++ tailWord_1643727) baseStart_1643727 baseEnd_1643727 := by
    simpa [prefixWord, tailWord_1643727, baseEnd_1643727] using wordTrace_append hprefix tailTrace_1643727
  have hstable : (prefixWord ++ tailWord_1643727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643727).length < 2 ^ (prefixWord ++ tailWord_1643727).sum := by decide
  have hdescent : baseEnd_1643727 < baseStart_1643727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643744 : List Nat := [2, 1, 1, 3, 1, 4, 1, 4, 4]
def baseStart_1643744 : Nat := 118140960795 + 1643744 * 2 ^ 59
def prefixEnd_1643744 : Nat := 4983230072969 + 3 ^ 40 * 1643744 * 2
def baseEnd_1643744 : Nat := 375124775530720923440251

theorem tailTrace_1643744 : CollatzResearch.WordTrace tailWord_1643744 prefixEnd_1643744 375124775530720923440251 := by
  unfold tailWord_1643744
  simp only [CollatzResearch.WordTrace]
  refine ⟨29976134478501845985161143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39968179304669127980214857 29976134478501845985161143)
  ·
    refine ⟨44964201717752768977741715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29976134478501845985161143 44964201717752768977741715)
    ·
      refine ⟨67446302576629153466612573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44964201717752768977741715 67446302576629153466612573)
      ·
        refine ⟨25292363466235932549979715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67446302576629153466612573 25292363466235932549979715)
        ·
          refine ⟨37938545199353898824969573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25292363466235932549979715 37938545199353898824969573)
          ·
            refine ⟨7113477224878856029681795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37938545199353898824969573 7113477224878856029681795)
            ·
              refine ⟨10670215837318284044522693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7113477224878856029681795 10670215837318284044522693)
              ·
                refine ⟨2000665469497178258348005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10670215837318284044522693 2000665469497178258348005)
                ·
                  refine ⟨375124775530720923440251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2000665469497178258348005 375124775530720923440251)
                  ·
                    rfl

theorem cell21_1643744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 4].length) (baseStart_1643744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1643744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1643744 prefixEnd_1643744 := by exact prefixLift 1643744
  have htrace : WordTrace (prefixWord ++ tailWord_1643744) baseStart_1643744 baseEnd_1643744 := by
    simpa [prefixWord, tailWord_1643744, baseEnd_1643744] using wordTrace_append hprefix tailTrace_1643744
  have hstable : (prefixWord ++ tailWord_1643744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643744).length < 2 ^ (prefixWord ++ tailWord_1643744).sum := by decide
  have hdescent : baseEnd_1643744 < baseStart_1643744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643775 : List Nat := [1, 1, 2, 2, 1, 6, 3, 5]
def baseStart_1643775 : Nat := 118140960795 + 1643775 * 2 ^ 59
def prefixEnd_1643775 : Nat := 4983230072969 + 3 ^ 40 * 1643775 * 2
def baseEnd_1643775 : Nat := 125043950051023919474507

theorem tailTrace_1643775 : CollatzResearch.WordTrace tailWord_1643775 prefixEnd_1643775 125043950051023919474507 := by
  unfold tailWord_1643775
  simp only [CollatzResearch.WordTrace]
  refine ⟨59953399619891384264700779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39968933079927589509800519 59953399619891384264700779)
  ·
    refine ⟨89930099429837076397051169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59953399619891384264700779 89930099429837076397051169)
    ·
      refine ⟨67447574572377807297788377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89930099429837076397051169 67447574572377807297788377)
      ·
        refine ⟨50585680929283355473341283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67447574572377807297788377 50585680929283355473341283)
        ·
          refine ⟨75878521393925033210011925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50585680929283355473341283 75878521393925033210011925)
          ·
            refine ⟨3556805690340235931719309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 75878521393925033210011925 3556805690340235931719309)
            ·
              refine ⟨1333802133877588474394741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3556805690340235931719309 1333802133877588474394741)
              ·
                refine ⟨125043950051023919474507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1333802133877588474394741 125043950051023919474507)
                ·
                  rfl

theorem cell21_1643775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 5].length) (baseStart_1643775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1643775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1643775 prefixEnd_1643775 := by exact prefixLift 1643775
  have htrace : WordTrace (prefixWord ++ tailWord_1643775) baseStart_1643775 baseEnd_1643775 := by
    simpa [prefixWord, tailWord_1643775, baseEnd_1643775] using wordTrace_append hprefix tailTrace_1643775
  have hstable : (prefixWord ++ tailWord_1643775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643775).length < 2 ^ (prefixWord ++ tailWord_1643775).sum := by decide
  have hdescent : baseEnd_1643775 < baseStart_1643775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643834 : List Nat := [3, 1, 1, 1, 4, 1, 3, 7]
def baseStart_1643834 : Nat := 118140960795 + 1643834 * 2 ^ 59
def prefixEnd_1643834 : Nat := 4983230072969 + 3 ^ 40 * 1643834 * 2
def baseEnd_1643834 : Nat := 125048438252300255646689

theorem tailTrace_1643834 : CollatzResearch.WordTrace tailWord_1643834 prefixEnd_1643834 125048438252300255646689 := by
  unfold tailWord_1643834
  simp only [CollatzResearch.WordTrace]
  refine ⟨14988887881669409335274639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39970367684451758227399037 14988887881669409335274639)
  ·
    refine ⟨22483331822504114002911959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14988887881669409335274639 22483331822504114002911959)
    ·
      refine ⟨33724997733756171004367939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22483331822504114002911959 33724997733756171004367939)
      ·
        refine ⟨50587496600634256506551909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33724997733756171004367939 50587496600634256506551909)
        ·
          refine ⟨9485155612618923094978483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50587496600634256506551909 9485155612618923094978483)
          ·
            refine ⟨14227733418928384642467725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9485155612618923094978483 14227733418928384642467725)
            ·
              refine ⟨5335400032098144240925397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14227733418928384642467725 5335400032098144240925397)
              ·
                refine ⟨125048438252300255646689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5335400032098144240925397 125048438252300255646689)
                ·
                  rfl

theorem cell21_1643834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_1643834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1643834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1643834 prefixEnd_1643834 := by exact prefixLift 1643834
  have htrace : WordTrace (prefixWord ++ tailWord_1643834) baseStart_1643834 baseEnd_1643834 := by
    simpa [prefixWord, tailWord_1643834, baseEnd_1643834] using wordTrace_append hprefix tailTrace_1643834
  have hstable : (prefixWord ++ tailWord_1643834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643834).length < 2 ^ (prefixWord ++ tailWord_1643834).sum := by decide
  have hdescent : baseEnd_1643834 < baseStart_1643834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643865 : List Nat := [1, 2, 1, 2, 2, 2, 5, 1, 5]
def baseStart_1643865 : Nat := 118140960795 + 1643865 * 2 ^ 59
def prefixEnd_1643865 : Nat := 4983230072969 + 3 ^ 40 * 1643865 * 2
def baseEnd_1643865 : Nat := 375152389379251601923337

theorem tailTrace_1643865 : CollatzResearch.WordTrace tailWord_1643865 prefixEnd_1643865 375152389379251601923337 := by
  unfold tailWord_1643865
  simp only [CollatzResearch.WordTrace]
  refine ⟨59956682189565329635477049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39971121459710219756984699 59956682189565329635477049)
  ·
    refine ⟨44967511642173997226607787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59956682189565329635477049 44967511642173997226607787)
    ·
      refine ⟨67451267463260995839911681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44967511642173997226607787 67451267463260995839911681)
      ·
        refine ⟨50588450597445746879933761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67451267463260995839911681 50588450597445746879933761)
        ·
          refine ⟨37941337948084310159950321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50588450597445746879933761 37941337948084310159950321)
          ·
            refine ⟨28456003461063232619962741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37941337948084310159950321 28456003461063232619962741)
            ·
              refine ⟨2667750324474678058121507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28456003461063232619962741 2667750324474678058121507)
              ·
                refine ⟨4001625486712017087182261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2667750324474678058121507 4001625486712017087182261)
                ·
                  refine ⟨375152389379251601923337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4001625486712017087182261 375152389379251601923337)
                  ·
                    rfl

theorem cell21_1643865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 5].length) (baseStart_1643865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1643865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1643865 prefixEnd_1643865 := by exact prefixLift 1643865
  have htrace : WordTrace (prefixWord ++ tailWord_1643865) baseStart_1643865 baseEnd_1643865 := by
    simpa [prefixWord, tailWord_1643865, baseEnd_1643865] using wordTrace_append hprefix tailTrace_1643865
  have hstable : (prefixWord ++ tailWord_1643865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643865).length < 2 ^ (prefixWord ++ tailWord_1643865).sum := by decide
  have hdescent : baseEnd_1643865 < baseStart_1643865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643913 : List Nat := [1, 2, 1, 1, 7, 1, 2, 2, 4]
def baseStart_1643913 : Nat := 118140960795 + 1643913 * 2 ^ 59
def prefixEnd_1643913 : Nat := 4983230072969 + 3 ^ 40 * 1643913 * 2
def baseEnd_1643913 : Nat := 375163343633214185123239

theorem tailTrace_1643913 : CollatzResearch.WordTrace tailWord_1643913 prefixEnd_1643913 375163343633214185123239 := by
  unfold tailWord_1643913
  simp only [CollatzResearch.WordTrace]
  refine ⟨59958432893391433833224393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39972288595594289222149595 59958432893391433833224393)
  ·
    refine ⟨44968824670043575374918295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59958432893391433833224393 44968824670043575374918295)
    ·
      refine ⟨67453237005065363062377443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44968824670043575374918295 67453237005065363062377443)
      ·
        refine ⟨101179855507598044593566165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67453237005065363062377443 101179855507598044593566165)
        ·
          refine ⟨2371402863459329170161707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 101179855507598044593566165 2371402863459329170161707)
          ·
            refine ⟨3557104295188993755242561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2371402863459329170161707 3557104295188993755242561)
            ·
              refine ⟨2667828221391745316431921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3557104295188993755242561 2667828221391745316431921)
              ·
                refine ⟨2000871166043808987323941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2667828221391745316431921 2000871166043808987323941)
                ·
                  refine ⟨375163343633214185123239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2000871166043808987323941 375163343633214185123239)
                  ·
                    rfl

theorem cell21_1643913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 4].length) (baseStart_1643913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1643913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1643913 prefixEnd_1643913 := by exact prefixLift 1643913
  have htrace : WordTrace (prefixWord ++ tailWord_1643913) baseStart_1643913 baseEnd_1643913 := by
    simpa [prefixWord, tailWord_1643913, baseEnd_1643913] using wordTrace_append hprefix tailTrace_1643913
  have hstable : (prefixWord ++ tailWord_1643913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643913).length < 2 ^ (prefixWord ++ tailWord_1643913).sum := by decide
  have hdescent : baseEnd_1643913 < baseStart_1643913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643989 : List Nat := [1, 3, 2, 3, 1, 1, 5, 1, 4]
def baseStart_1643989 : Nat := 118140960795 + 1643989 * 2 ^ 59
def prefixEnd_1643989 : Nat := 4983230072969 + 3 ^ 40 * 1643989 * 2
def baseEnd_1643989 : Nat := 375180687868654941856417

theorem tailTrace_1643989 : CollatzResearch.WordTrace tailWord_1643989 prefixEnd_1643989 375180687868654941856417 := by
  unfold tailWord_1643989
  simp only [CollatzResearch.WordTrace]
  refine ⟨59961204841116098812991021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39974136560744065875327347 59961204841116098812991021)
  ·
    refine ⟨22485451815418537054871633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59961204841116098812991021 22485451815418537054871633)
    ·
      refine ⟨16864088861563902791153725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22485451815418537054871633 16864088861563902791153725)
      ·
        refine ⟨6324033323086463546682647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16864088861563902791153725 6324033323086463546682647)
        ·
          refine ⟨9486049984629695320023971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6324033323086463546682647 9486049984629695320023971)
          ·
            refine ⟨14229074976944542980035957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9486049984629695320023971 14229074976944542980035957)
            ·
              refine ⟨1333975779088550904378371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14229074976944542980035957 1333975779088550904378371)
              ·
                refine ⟨2000963668632826356567557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1333975779088550904378371 2000963668632826356567557)
                ·
                  refine ⟨375180687868654941856417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2000963668632826356567557 375180687868654941856417)
                  ·
                    rfl

theorem cell21_1643989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_1643989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1643989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1643989 prefixEnd_1643989 := by exact prefixLift 1643989
  have htrace : WordTrace (prefixWord ++ tailWord_1643989) baseStart_1643989 baseEnd_1643989 := by
    simpa [prefixWord, tailWord_1643989, baseEnd_1643989] using wordTrace_append hprefix tailTrace_1643989
  have hstable : (prefixWord ++ tailWord_1643989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643989).length < 2 ^ (prefixWord ++ tailWord_1643989).sum := by decide
  have hdescent : baseEnd_1643989 < baseStart_1643989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644000 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 7]
def baseStart_1644000 : Nat := 118140960795 + 1644000 * 2 ^ 59
def prefixEnd_1644000 : Nat := 4983230072969 + 3 ^ 40 * 1644000 * 2
def baseEnd_1644000 : Nat := 375183198218521367173061

theorem tailTrace_1644000 : CollatzResearch.WordTrace tailWord_1644000 prefixEnd_1644000 375183198218521367173061 := by
  unfold tailWord_1644000
  simp only [CollatzResearch.WordTrace]
  refine ⟨29980803022038123845820727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39974404029384165127760969 29980803022038123845820727)
  ·
    refine ⟨44971204533057185768731091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29980803022038123845820727 44971204533057185768731091)
    ·
      refine ⟨67456806799585778653096637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44971204533057185768731091 67456806799585778653096637)
      ·
        refine ⟨25296302549844666994911239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67456806799585778653096637 25296302549844666994911239)
        ·
          refine ⟨37944453824767000492366859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25296302549844666994911239 37944453824767000492366859)
          ·
            refine ⟨56916680737150500738550289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37944453824767000492366859 56916680737150500738550289)
            ·
              refine ⟨42687510552862875553912717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56916680737150500738550289 42687510552862875553912717)
              ·
                refine ⟨16007816457323578332717269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42687510552862875553912717 16007816457323578332717269)
                ·
                  refine ⟨375183198218521367173061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16007816457323578332717269 375183198218521367173061)
                  ·
                    rfl

theorem cell21_1644000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_1644000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1644000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1644000 prefixEnd_1644000 := by exact prefixLift 1644000
  have htrace : WordTrace (prefixWord ++ tailWord_1644000) baseStart_1644000 baseEnd_1644000 := by
    simpa [prefixWord, tailWord_1644000, baseEnd_1644000] using wordTrace_append hprefix tailTrace_1644000
  have hstable : (prefixWord ++ tailWord_1644000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644000).length < 2 ^ (prefixWord ++ tailWord_1644000).sum := by decide
  have hdescent : baseEnd_1644000 < baseStart_1644000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644003 : List Nat := [1, 1, 1, 6, 2, 1, 4, 5]
def baseStart_1644003 : Nat := 118140960795 + 1644003 * 2 ^ 59
def prefixEnd_1644003 : Nat := 4983230072969 + 3 ^ 40 * 1644003 * 2
def baseEnd_1644003 : Nat := 125061294286464676207685

theorem tailTrace_1644003 : CollatzResearch.WordTrace tailWord_1644003 prefixEnd_1644003 125061294286464676207685 := by
  unfold tailWord_1644003
  simp only [CollatzResearch.WordTrace]
  refine ⟨59961715463065379204000663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39974476975376919469333775 59961715463065379204000663)
  ·
    refine ⟨89942573194598068806000995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59961715463065379204000663 89942573194598068806000995)
    ·
      refine ⟨134913859791897103209001493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89942573194598068806000995 134913859791897103209001493)
      ·
        refine ⟨6324087177745176712921945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 134913859791897103209001493 6324087177745176712921945)
        ·
          refine ⟨4743065383308882534691459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6324087177745176712921945 4743065383308882534691459)
          ·
            refine ⟨7114598074963323802037189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4743065383308882534691459 7114598074963323802037189)
            ·
              refine ⟨1333987139055623212881973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7114598074963323802037189 1333987139055623212881973)
              ·
                refine ⟨125061294286464676207685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1333987139055623212881973 125061294286464676207685)
                ·
                  rfl

theorem cell21_1644003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 5].length) (baseStart_1644003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1644003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1644003 prefixEnd_1644003 := by exact prefixLift 1644003
  have htrace : WordTrace (prefixWord ++ tailWord_1644003) baseStart_1644003 baseEnd_1644003 := by
    simpa [prefixWord, tailWord_1644003, baseEnd_1644003] using wordTrace_append hprefix tailTrace_1644003
  have hstable : (prefixWord ++ tailWord_1644003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644003).length < 2 ^ (prefixWord ++ tailWord_1644003).sum := by decide
  have hdescent : baseEnd_1644003 < baseStart_1644003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644121 : List Nat := [1, 2, 1, 2, 2, 1, 1, 11]
def baseStart_1644121 : Nat := 118140960795 + 1644121 * 2 ^ 59
def prefixEnd_1644121 : Nat := 4983230072969 + 3 ^ 40 * 1644121 * 2
def baseEnd_1644121 : Nat := 125070270689017348552049

theorem tailTrace_1644121 : CollatzResearch.WordTrace tailWord_1644121 prefixEnd_1644121 125070270689017348552049 := by
  unfold tailWord_1644121
  simp only [CollatzResearch.WordTrace]
  refine ⟨59966019276637885356796217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39977346184425256904530811 59966019276637885356796217)
  ·
    refine ⟨44974514457478414017597163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59966019276637885356796217 44974514457478414017597163)
    ·
      refine ⟨67461771686217621026395745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44974514457478414017597163 67461771686217621026395745)
      ·
        refine ⟨50596328764663215769796809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67461771686217621026395745 50596328764663215769796809)
        ·
          refine ⟨37947246573497411827347607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50596328764663215769796809 37947246573497411827347607)
          ·
            refine ⟨56920869860246117741021411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37947246573497411827347607 56920869860246117741021411)
            ·
              refine ⟨85381304790369176611532117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56920869860246117741021411 85381304790369176611532117)
              ·
                refine ⟨125070270689017348552049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 85381304790369176611532117 125070270689017348552049)
                ·
                  rfl

theorem cell21_1644121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 11].length) (baseStart_1644121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1644121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1644121 prefixEnd_1644121 := by exact prefixLift 1644121
  have htrace : WordTrace (prefixWord ++ tailWord_1644121) baseStart_1644121 baseEnd_1644121 := by
    simpa [prefixWord, tailWord_1644121, baseEnd_1644121] using wordTrace_append hprefix tailTrace_1644121
  have hstable : (prefixWord ++ tailWord_1644121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644121).length < 2 ^ (prefixWord ++ tailWord_1644121).sum := by decide
  have hdescent : baseEnd_1644121 < baseStart_1644121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644138 : List Nat := [3, 1, 3, 2, 1, 3, 8]
def baseStart_1644138 : Nat := 118140960795 + 1644138 * 2 ^ 59
def prefixEnd_1644138 : Nat := 4983230072969 + 3 ^ 40 * 1644138 * 2
def baseEnd_1644138 : Nat := 41690521299851532652531

theorem tailTrace_1644138 : CollatzResearch.WordTrace tailWord_1644138 prefixEnd_1644138 41690521299851532652531 := by
  unfold tailWord_1644138
  simp only [CollatzResearch.WordTrace]
  refine ⟨14991659829394074315041267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39977759545050864840110045 14991659829394074315041267)
  ·
    refine ⟨22487489744091111472561901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14991659829394074315041267 22487489744091111472561901)
    ·
      refine ⟨8432808654034166802210713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22487489744091111472561901 8432808654034166802210713)
      ·
        refine ⟨6324606490525625101658035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8432808654034166802210713 6324606490525625101658035)
        ·
          refine ⟨9486909735788437652487053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6324606490525625101658035 9486909735788437652487053)
          ·
            refine ⟨3557591150920664119682645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9486909735788437652487053 3557591150920664119682645)
            ·
              refine ⟨41690521299851532652531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3557591150920664119682645 41690521299851532652531)
              ·
                rfl

theorem cell21_1644138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 8].length) (baseStart_1644138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1644138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1644138 prefixEnd_1644138 := by exact prefixLift 1644138
  have htrace : WordTrace (prefixWord ++ tailWord_1644138) baseStart_1644138 baseEnd_1644138 := by
    simpa [prefixWord, tailWord_1644138, baseEnd_1644138] using wordTrace_append hprefix tailTrace_1644138
  have hstable : (prefixWord ++ tailWord_1644138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644138).length < 2 ^ (prefixWord ++ tailWord_1644138).sum := by decide
  have hdescent : baseEnd_1644138 < baseStart_1644138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644183 : List Nat := [1, 1, 3, 3, 2, 2, 1, 2, 6]
def baseStart_1644183 : Nat := 118140960795 + 1644183 * 2 ^ 59
def prefixEnd_1644183 : Nat := 4983230072969 + 3 ^ 40 * 1644183 * 2
def baseEnd_1644183 : Nat := 375224961311753715622687

theorem tailTrace_1644183 : CollatzResearch.WordTrace tailWord_1644183 prefixEnd_1644183 375224961311753715622687 := by
  unfold tailWord_1644183
  simp only [CollatzResearch.WordTrace]
  refine ⟨59968280602413269945553203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39978853734942179963702135 59968280602413269945553203)
  ·
    refine ⟨89952420903619904918329805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59968280602413269945553203 89952420903619904918329805)
    ·
      refine ⟨33732157838857464344373677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89952420903619904918329805 33732157838857464344373677)
      ·
        refine ⟨12649559189571549129140129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33732157838857464344373677 12649559189571549129140129)
        ·
          refine ⟨9487169392178661846855097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12649559189571549129140129 9487169392178661846855097)
          ·
            refine ⟨7115377044133996385141323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9487169392178661846855097 7115377044133996385141323)
            ·
              refine ⟨10673065566200994577711985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7115377044133996385141323 10673065566200994577711985)
              ·
                refine ⟨8004799174650745933283989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10673065566200994577711985 8004799174650745933283989)
                ·
                  refine ⟨375224961311753715622687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8004799174650745933283989 375224961311753715622687)
                  ·
                    rfl

theorem cell21_1644183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 6].length) (baseStart_1644183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1644183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1644183 prefixEnd_1644183 := by exact prefixLift 1644183
  have htrace : WordTrace (prefixWord ++ tailWord_1644183) baseStart_1644183 baseEnd_1644183 := by
    simpa [prefixWord, tailWord_1644183, baseEnd_1644183] using wordTrace_append hprefix tailTrace_1644183
  have hstable : (prefixWord ++ tailWord_1644183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644183).length < 2 ^ (prefixWord ++ tailWord_1644183).sum := by decide
  have hdescent : baseEnd_1644183 < baseStart_1644183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644197 : List Nat := [1, 3, 1, 2, 1, 2, 11]
def baseStart_1644197 : Nat := 118140960795 + 1644197 * 2 ^ 59
def prefixEnd_1644197 : Nat := 4983230072969 + 3 ^ 40 * 1644197 * 2
def baseEnd_1644197 : Nat := 41692017366943644709925

theorem tailTrace_1644197 : CollatzResearch.WordTrace tailWord_1644197 prefixEnd_1644197 41692017366943644709925 := by
  unfold tailWord_1644197
  simp only [CollatzResearch.WordTrace]
  refine ⟨59968791224362550336562845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39979194149575033557708563 59968791224362550336562845)
  ·
    refine ⟨22488296709135956376211067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59968791224362550336562845 22488296709135956376211067)
    ·
      refine ⟨33732445063703934564316601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22488296709135956376211067 33732445063703934564316601)
      ·
        refine ⟨25299333797777950923237451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33732445063703934564316601 25299333797777950923237451)
        ·
          refine ⟨37949000696666926384856177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25299333797777950923237451 37949000696666926384856177)
          ·
            refine ⟨28461750522500194788642133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37949000696666926384856177 28461750522500194788642133)
            ·
              refine ⟨41692017366943644709925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 28461750522500194788642133 41692017366943644709925)
              ·
                rfl

theorem cell21_1644197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 11].length) (baseStart_1644197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1644197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1644197 prefixEnd_1644197 := by exact prefixLift 1644197
  have htrace : WordTrace (prefixWord ++ tailWord_1644197) baseStart_1644197 baseEnd_1644197 := by
    simpa [prefixWord, tailWord_1644197, baseEnd_1644197] using wordTrace_append hprefix tailTrace_1644197
  have hstable : (prefixWord ++ tailWord_1644197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644197).length < 2 ^ (prefixWord ++ tailWord_1644197).sum := by decide
  have hdescent : baseEnd_1644197 < baseStart_1644197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644321 : List Nat := [1, 2, 3, 2, 1, 4, 2, 1, 5]
def baseStart_1644321 : Nat := 118140960795 + 1644321 * 2 ^ 59
def prefixEnd_1644321 : Nat := 4983230072969 + 3 ^ 40 * 1644321 * 2
def baseEnd_1644321 : Nat := 375256454791896142322405

theorem tailTrace_1644321 : CollatzResearch.WordTrace tailWord_1644321 prefixEnd_1644321 375256454791896142322405 := by
  unfold tailWord_1644321
  simp only [CollatzResearch.WordTrace]
  refine ⟨59973313875913319514076817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39982209250608879676051211 59973313875913319514076817)
  ·
    refine ⟨44979985406934989635557613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59973313875913319514076817 44979985406934989635557613)
    ·
      refine ⟨16867494527600621113334105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44979985406934989635557613 16867494527600621113334105)
      ·
        refine ⟨12650620895700465835000579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16867494527600621113334105 12650620895700465835000579)
        ·
          refine ⟨18975931343550698752500869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12650620895700465835000579 18975931343550698752500869)
          ·
            refine ⟨3557987126915756016093913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18975931343550698752500869 3557987126915756016093913)
            ·
              refine ⟨2668490345186817012070435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3557987126915756016093913 2668490345186817012070435)
              ·
                refine ⟨4002735517780225518105653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2668490345186817012070435 4002735517780225518105653)
                ·
                  refine ⟨375256454791896142322405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4002735517780225518105653 375256454791896142322405)
                  ·
                    rfl

theorem cell21_1644321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 5].length) (baseStart_1644321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1644321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1644321 prefixEnd_1644321 := by exact prefixLift 1644321
  have htrace : WordTrace (prefixWord ++ tailWord_1644321) baseStart_1644321 baseEnd_1644321 := by
    simpa [prefixWord, tailWord_1644321, baseEnd_1644321] using wordTrace_append hprefix tailTrace_1644321
  have hstable : (prefixWord ++ tailWord_1644321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644321).length < 2 ^ (prefixWord ++ tailWord_1644321).sum := by decide
  have hdescent : baseEnd_1644321 < baseStart_1644321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644386 : List Nat := [3, 3, 2, 1, 2, 3, 2, 1, 4]
def baseStart_1644386 : Nat := 118140960795 + 1644386 * 2 ^ 59
def prefixEnd_1644386 : Nat := 4983230072969 + 3 ^ 40 * 1644386 * 2
def baseEnd_1644386 : Nat := 375271288677470473738939

theorem tailTrace_1644386 : CollatzResearch.WordTrace tailWord_1644386 prefixEnd_1644386 375271288677470473738939 := by
  unfold tailWord_1644386
  simp only [CollatzResearch.WordTrace]
  refine ⟨14993921155169458903798253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39983789747118557076795341 14993921155169458903798253)
  ·
    refine ⟨5622720433188547088924345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14993921155169458903798253 5622720433188547088924345)
    ·
      refine ⟨4217040324891410316693259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5622720433188547088924345 4217040324891410316693259)
      ·
        refine ⟨6325560487337115475039889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4217040324891410316693259 6325560487337115475039889)
        ·
          refine ⟨4744170365502836606279917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6325560487337115475039889 4744170365502836606279917)
          ·
            refine ⟨1779063887063563727354969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4744170365502836606279917 1779063887063563727354969)
            ·
              refine ⟨1334297915297672795516227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1779063887063563727354969 1334297915297672795516227)
              ·
                refine ⟨2001446872946509193274341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1334297915297672795516227 2001446872946509193274341)
                ·
                  refine ⟨375271288677470473738939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2001446872946509193274341 375271288677470473738939)
                  ·
                    rfl

theorem cell21_1644386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_1644386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1644386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1644386 prefixEnd_1644386 := by exact prefixLift 1644386
  have htrace : WordTrace (prefixWord ++ tailWord_1644386) baseStart_1644386 baseEnd_1644386 := by
    simpa [prefixWord, tailWord_1644386, baseEnd_1644386] using wordTrace_append hprefix tailTrace_1644386
  have hstable : (prefixWord ++ tailWord_1644386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644386).length < 2 ^ (prefixWord ++ tailWord_1644386).sum := by decide
  have hdescent : baseEnd_1644386 < baseStart_1644386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644442 : List Nat := [3, 1, 1, 4, 2, 1, 3, 6]
def baseStart_1644442 : Nat := 118140960795 + 1644442 * 2 ^ 59
def prefixEnd_1644442 : Nat := 4983230072969 + 3 ^ 40 * 1644442 * 2
def baseEnd_1644442 : Nat := 125094689546808940268497

theorem tailTrace_1644442 : CollatzResearch.WordTrace tailWord_1644442 prefixEnd_1644442 125094689546808940268497 := by
  unfold tailWord_1644442
  simp only [CollatzResearch.WordTrace]
  refine ⟨14994431777118739294807895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39985151405649971452821053 14994431777118739294807895)
  ·
    refine ⟨22491647665678108942211843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14994431777118739294807895 22491647665678108942211843)
    ·
      refine ⟨33737471498517163413317765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22491647665678108942211843 33737471498517163413317765)
      ·
        refine ⟨6325775905971968139997081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33737471498517163413317765 6325775905971968139997081)
        ·
          refine ⟨4744331929478976104997811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6325775905971968139997081 4744331929478976104997811)
          ·
            refine ⟨7116497894218464157496717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4744331929478976104997811 7116497894218464157496717)
            ·
              refine ⟨2668686710331924059061269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7116497894218464157496717 2668686710331924059061269)
              ·
                refine ⟨125094689546808940268497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2668686710331924059061269 125094689546808940268497)
                ·
                  rfl

theorem cell21_1644442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 6].length) (baseStart_1644442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1644442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1644442 prefixEnd_1644442 := by exact prefixLift 1644442
  have htrace : WordTrace (prefixWord ++ tailWord_1644442) baseStart_1644442 baseEnd_1644442 := by
    simpa [prefixWord, tailWord_1644442, baseEnd_1644442] using wordTrace_append hprefix tailTrace_1644442
  have hstable : (prefixWord ++ tailWord_1644442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644442).length < 2 ^ (prefixWord ++ tailWord_1644442).sum := by decide
  have hdescent : baseEnd_1644442 < baseStart_1644442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644504 : List Nat := [2, 1, 2, 2, 2, 2, 5, 1, 4]
def baseStart_1644504 : Nat := 118140960795 + 1644504 * 2 ^ 59
def prefixEnd_1644504 : Nat := 4983230072969 + 3 ^ 40 * 1644504 * 2
def baseEnd_1644504 : Nat := 375298217885128490772031

theorem tailTrace_1644504 : CollatzResearch.WordTrace tailWord_1644504 prefixEnd_1644504 375298217885128490772031 := by
  unfold tailWord_1644504
  simp only [CollatzResearch.WordTrace]
  refine ⟨29989994217125170883994283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39986658956166894511992377 29989994217125170883994283)
  ·
    refine ⟨44984991325687756325991425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29989994217125170883994283 44984991325687756325991425)
    ·
      refine ⟨33738743494265817244493569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44984991325687756325991425 33738743494265817244493569)
      ·
        refine ⟨25304057620699362933370177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33738743494265817244493569 25304057620699362933370177)
        ·
          refine ⟨18978043215524522200027633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25304057620699362933370177 18978043215524522200027633)
          ·
            refine ⟨14233532411643391650020725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18978043215524522200027633 14233532411643391650020725)
            ·
              refine ⟨1334393663591567967189443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14233532411643391650020725 1334393663591567967189443)
              ·
                refine ⟨2001590495387351950784165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1334393663591567967189443 2001590495387351950784165)
                ·
                  refine ⟨375298217885128490772031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2001590495387351950784165 375298217885128490772031)
                  ·
                    rfl

theorem cell21_1644504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 4].length) (baseStart_1644504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1644504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1644504 prefixEnd_1644504 := by exact prefixLift 1644504
  have htrace : WordTrace (prefixWord ++ tailWord_1644504) baseStart_1644504 baseEnd_1644504 := by
    simpa [prefixWord, tailWord_1644504, baseEnd_1644504] using wordTrace_append hprefix tailTrace_1644504
  have hstable : (prefixWord ++ tailWord_1644504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644504).length < 2 ^ (prefixWord ++ tailWord_1644504).sum := by decide
  have hdescent : baseEnd_1644504 < baseStart_1644504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644549 : List Nat := [1, 3, 1, 1, 2, 6, 1, 1, 5]
def baseStart_1644549 : Nat := 118140960795 + 1644549 * 2 ^ 59
def prefixEnd_1644549 : Nat := 4983230072969 + 3 ^ 40 * 1644549 * 2
def baseEnd_1644549 : Nat := 375308487498218412521939

theorem tailTrace_1644549 : CollatzResearch.WordTrace tailWord_1644549 prefixEnd_1644549 375308487498218412521939 := by
  unfold tailWord_1644549
  simp only [CollatzResearch.WordTrace]
  refine ⟨59981629719087314453376701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39987753146058209635584467 59981629719087314453376701)
  ·
    refine ⟨22493111144657742920016263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59981629719087314453376701 22493111144657742920016263)
    ·
      refine ⟨33739666716986614380024395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22493111144657742920016263 33739666716986614380024395)
      ·
        refine ⟨50609500075479921570036593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33739666716986614380024395 50609500075479921570036593)
        ·
          refine ⟨37957125056609941177527445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50609500075479921570036593 37957125056609941177527445)
          ·
            refine ⟨1779240237028590992696599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37957125056609941177527445 1779240237028590992696599)
            ·
              refine ⟨2668860355542886489044899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1779240237028590992696599 2668860355542886489044899)
              ·
                refine ⟨4003290533314329733567349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2668860355542886489044899 4003290533314329733567349)
                ·
                  refine ⟨375308487498218412521939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4003290533314329733567349 375308487498218412521939)
                  ·
                    rfl

theorem cell21_1644549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_1644549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1644549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1644549 prefixEnd_1644549 := by exact prefixLift 1644549
  have htrace : WordTrace (prefixWord ++ tailWord_1644549) baseStart_1644549 baseEnd_1644549 := by
    simpa [prefixWord, tailWord_1644549, baseEnd_1644549] using wordTrace_append hprefix tailTrace_1644549
  have hstable : (prefixWord ++ tailWord_1644549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644549).length < 2 ^ (prefixWord ++ tailWord_1644549).sum := by decide
  have hdescent : baseEnd_1644549 < baseStart_1644549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644591 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 9]
def baseStart_1644591 : Nat := 118140960795 + 1644591 * 2 ^ 59
def prefixEnd_1644591 : Nat := 4983230072969 + 3 ^ 40 * 1644591 * 2
def baseEnd_1644591 : Nat := 375318072470435672821853

theorem tailTrace_1644591 : CollatzResearch.WordTrace tailWord_1644591 prefixEnd_1644591 375318072470435672821853 := by
  unfold tailWord_1644591
  simp only [CollatzResearch.WordTrace]
  refine ⟨59983161584935155626405627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39988774389956770417603751 59983161584935155626405627)
  ·
    refine ⟨89974742377402733439608441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59983161584935155626405627 89974742377402733439608441)
    ·
      refine ⟨67481056783052050079706331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89974742377402733439608441 67481056783052050079706331)
      ·
        refine ⟨101221585174578075119559497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67481056783052050079706331 101221585174578075119559497)
        ·
          refine ⟨75916188880933556339669623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101221585174578075119559497 75916188880933556339669623)
          ·
            refine ⟨113874283321400334509504435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75916188880933556339669623 113874283321400334509504435)
            ·
              refine ⟨170811424982100501764256653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113874283321400334509504435 170811424982100501764256653)
              ·
                refine ⟨64054284368287688161596245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170811424982100501764256653 64054284368287688161596245)
                ·
                  refine ⟨375318072470435672821853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64054284368287688161596245 375318072470435672821853)
                  ·
                    rfl

theorem cell21_1644591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 9].length) (baseStart_1644591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1644591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1644591 prefixEnd_1644591 := by exact prefixLift 1644591
  have htrace : WordTrace (prefixWord ++ tailWord_1644591) baseStart_1644591 baseEnd_1644591 := by
    simpa [prefixWord, tailWord_1644591, baseEnd_1644591] using wordTrace_append hprefix tailTrace_1644591
  have hstable : (prefixWord ++ tailWord_1644591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644591).length < 2 ^ (prefixWord ++ tailWord_1644591).sum := by decide
  have hdescent : baseEnd_1644591 < baseStart_1644591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644600 : List Nat := [2, 1, 2, 1, 7, 1, 2, 2, 3]
def baseStart_1644600 : Nat := 118140960795 + 1644600 * 2 ^ 59
def prefixEnd_1644600 : Nat := 4983230072969 + 3 ^ 40 * 1644600 * 2
def baseEnd_1644600 : Nat := 375320126393053657171835

theorem tailTrace_1644600 : CollatzResearch.WordTrace tailWord_1644600 prefixEnd_1644600 375320126393053657171835 := by
  unfold tailWord_1644600
  simp only [CollatzResearch.WordTrace]
  refine ⟨29991744920951275081741627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39988993227935033442322169 29991744920951275081741627)
  ·
    refine ⟨44987617381426912622612441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29991744920951275081741627 44987617381426912622612441)
    ·
      refine ⟨33740713036070184466959331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44987617381426912622612441 33740713036070184466959331)
      ·
        refine ⟨50611069554105276700438997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33740713036070184466959331 50611069554105276700438997)
        ·
          refine ⟨1186196942674342422666539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 50611069554105276700438997 1186196942674342422666539)
          ·
            refine ⟨1779295414011513633999809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1186196942674342422666539 1779295414011513633999809)
            ·
              refine ⟨1334471560508635225499857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1779295414011513633999809 1334471560508635225499857)
              ·
                refine ⟨1000853670381476419124893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1334471560508635225499857 1000853670381476419124893)
                ·
                  refine ⟨375320126393053657171835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1000853670381476419124893 375320126393053657171835)
                  ·
                    rfl

theorem cell21_1644600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2, 3].length) (baseStart_1644600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1644600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1644600 prefixEnd_1644600 := by exact prefixLift 1644600
  have htrace : WordTrace (prefixWord ++ tailWord_1644600) baseStart_1644600 baseEnd_1644600 := by
    simpa [prefixWord, tailWord_1644600, baseEnd_1644600] using wordTrace_append hprefix tailTrace_1644600
  have hstable : (prefixWord ++ tailWord_1644600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644600).length < 2 ^ (prefixWord ++ tailWord_1644600).sum := by decide
  have hdescent : baseEnd_1644600 < baseStart_1644600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644653 : List Nat := [1, 5, 1, 1, 2, 1, 10]
def baseStart_1644653 : Nat := 118140960795 + 1644653 * 2 ^ 59
def prefixEnd_1644653 : Nat := 4983230072969 + 3 ^ 40 * 1644653 * 2
def baseEnd_1644653 : Nat := 41703580190570815865377

theorem tailTrace_1644653 : CollatzResearch.WordTrace tailWord_1644653 prefixEnd_1644653 41703580190570815865377 := by
  unfold tailWord_1644653
  simp only [CollatzResearch.WordTrace]
  refine ⟨59985422910710540215162613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39990281940473693476775075 59985422910710540215162613)
  ·
    refine ⟨5623633397879113145171495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59985422910710540215162613 5623633397879113145171495)
    ·
      refine ⟨8435450096818669717757243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5623633397879113145171495 8435450096818669717757243)
      ·
        refine ⟨12653175145228004576635865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8435450096818669717757243 12653175145228004576635865)
        ·
          refine ⟨9489881358921003432476899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12653175145228004576635865 9489881358921003432476899)
          ·
            refine ⟨14234822038381505148715349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9489881358921003432476899 14234822038381505148715349)
            ·
              refine ⟨41703580190570815865377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14234822038381505148715349 41703580190570815865377)
              ·
                rfl

theorem cell21_1644653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 10].length) (baseStart_1644653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1644653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1644653 prefixEnd_1644653 := by exact prefixLift 1644653
  have htrace : WordTrace (prefixWord ++ tailWord_1644653) baseStart_1644653 baseEnd_1644653 := by
    simpa [prefixWord, tailWord_1644653, baseEnd_1644653] using wordTrace_append hprefix tailTrace_1644653
  have hstable : (prefixWord ++ tailWord_1644653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644653).length < 2 ^ (prefixWord ++ tailWord_1644653).sum := by decide
  have hdescent : baseEnd_1644653 < baseStart_1644653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644656 : List Nat := [2, 1, 1, 1, 5, 4, 1, 2, 4]
def baseStart_1644656 : Nat := 118140960795 + 1644656 * 2 ^ 59
def prefixEnd_1644656 : Nat := 4983230072969 + 3 ^ 40 * 1644656 * 2
def baseEnd_1644656 : Nat := 375332906356010004238387

theorem tailTrace_1644656 : CollatzResearch.WordTrace tailWord_1644656 prefixEnd_1644656 375332906356010004238387 := by
  unfold tailWord_1644656
  simp only [CollatzResearch.WordTrace]
  refine ⟨29992766164849835863760911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39990354886466447818347881 29992766164849835863760911)
  ·
    refine ⟨44989149247274753795641367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29992766164849835863760911 44989149247274753795641367)
    ·
      refine ⟨67483723870912130693462051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44989149247274753795641367 67483723870912130693462051)
      ·
        refine ⟨101225585806368196040193077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67483723870912130693462051 101225585806368196040193077)
        ·
          refine ⟨9489898669347018378768101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101225585806368196040193077 9489898669347018378768101)
          ·
            refine ⟨1779356000502565946019019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9489898669347018378768101 1779356000502565946019019)
            ·
              refine ⟨2669034000753848919028529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1779356000502565946019019 2669034000753848919028529)
              ·
                refine ⟨2001775500565386689271397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2669034000753848919028529 2001775500565386689271397)
                ·
                  refine ⟨375332906356010004238387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2001775500565386689271397 375332906356010004238387)
                  ·
                    rfl

theorem cell21_1644656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 4].length) (baseStart_1644656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1644656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1644656 prefixEnd_1644656 := by exact prefixLift 1644656
  have htrace : WordTrace (prefixWord ++ tailWord_1644656) baseStart_1644656 baseEnd_1644656 := by
    simpa [prefixWord, tailWord_1644656, baseEnd_1644656] using wordTrace_append hprefix tailTrace_1644656
  have hstable : (prefixWord ++ tailWord_1644656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644656).length < 2 ^ (prefixWord ++ tailWord_1644656).sum := by decide
  have hdescent : baseEnd_1644656 < baseStart_1644656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644673 : List Nat := [1, 2, 4, 2, 3, 1, 3, 1, 4]
def baseStart_1644673 : Nat := 118140960795 + 1644673 * 2 ^ 59
def prefixEnd_1644673 : Nat := 4983230072969 + 3 ^ 40 * 1644673 * 2
def baseEnd_1644673 : Nat := 375336785987621752455019

theorem tailTrace_1644673 : CollatzResearch.WordTrace tailWord_1644673 prefixEnd_1644673 375336785987621752455019 := by
  unfold tailWord_1644673
  simp only [CollatzResearch.WordTrace]
  refine ⟨59986152370638083630890673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39990768247092055753927115 59986152370638083630890673)
  ·
    refine ⟨44989614277978562723168005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59986152370638083630890673 44989614277978562723168005)
    ·
      refine ⟨8435552677120980510594001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44989614277978562723168005 8435552677120980510594001)
      ·
        refine ⟨6326664507840735382945501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8435552677120980510594001 6326664507840735382945501)
        ·
          refine ⟨2372499190440275768604563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6326664507840735382945501 2372499190440275768604563)
          ·
            refine ⟨3558748785660413652906845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2372499190440275768604563 3558748785660413652906845)
            ·
              refine ⟨1334530794622655119840067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3558748785660413652906845 1334530794622655119840067)
              ·
                refine ⟨2001796191933982679760101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1334530794622655119840067 2001796191933982679760101)
                ·
                  refine ⟨375336785987621752455019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2001796191933982679760101 375336785987621752455019)
                  ·
                    rfl

theorem cell21_1644673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 4].length) (baseStart_1644673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1644673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1644673 prefixEnd_1644673 := by exact prefixLift 1644673
  have htrace : WordTrace (prefixWord ++ tailWord_1644673) baseStart_1644673 baseEnd_1644673 := by
    simpa [prefixWord, tailWord_1644673, baseEnd_1644673] using wordTrace_append hprefix tailTrace_1644673
  have hstable : (prefixWord ++ tailWord_1644673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644673).length < 2 ^ (prefixWord ++ tailWord_1644673).sum := by decide
  have hdescent : baseEnd_1644673 < baseStart_1644673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644724 : List Nat := [2, 5, 3, 1, 1, 2, 2, 1, 4]
def baseStart_1644724 : Nat := 118140960795 + 1644724 * 2 ^ 59
def prefixEnd_1644724 : Nat := 4983230072969 + 3 ^ 40 * 1644724 * 2
def baseEnd_1644724 : Nat := 375348424882456997104915

theorem tailTrace_1644724 : CollatzResearch.WordTrace tailWord_1644724 prefixEnd_1644724 375348424882456997104915 := by
  unfold tailWord_1644724
  simp only [CollatzResearch.WordTrace]
  refine ⟨29994006246726659670498613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39992008328968879560664817 29994006246726659670498613)
  ·
    refine ⟨2811938085630624344109245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29994006246726659670498613 2811938085630624344109245)
    ·
      refine ⟨1054476782111484129040967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2811938085630624344109245 1054476782111484129040967)
      ·
        refine ⟨1581715173167226193561451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1054476782111484129040967 1581715173167226193561451)
        ·
          refine ⟨2372572759750839290342177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1581715173167226193561451 2372572759750839290342177)
          ·
            refine ⟨1779429569813129467756633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2372572759750839290342177 1779429569813129467756633)
            ·
              refine ⟨1334572177359847100817475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1779429569813129467756633 1334572177359847100817475)
              ·
                refine ⟨2001858266039770651226213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1334572177359847100817475 2001858266039770651226213)
                ·
                  refine ⟨375348424882456997104915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2001858266039770651226213 375348424882456997104915)
                  ·
                    rfl

theorem cell21_1644724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_1644724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1644724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1644724 prefixEnd_1644724 := by exact prefixLift 1644724
  have htrace : WordTrace (prefixWord ++ tailWord_1644724) baseStart_1644724 baseEnd_1644724 := by
    simpa [prefixWord, tailWord_1644724, baseEnd_1644724] using wordTrace_append hprefix tailTrace_1644724
  have hstable : (prefixWord ++ tailWord_1644724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644724).length < 2 ^ (prefixWord ++ tailWord_1644724).sum := by decide
  have hdescent : baseEnd_1644724 < baseStart_1644724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644729 : List Nat := [1, 2, 1, 4, 1, 2, 4, 6]
def baseStart_1644729 : Nat := 118140960795 + 1644729 * 2 ^ 59
def prefixEnd_1644729 : Nat := 4983230072969 + 3 ^ 40 * 1644729 * 2
def baseEnd_1644729 : Nat := 125116521983526033173857

theorem tailTrace_1644729 : CollatzResearch.WordTrace tailWord_1644729 prefixEnd_1644729 125116521983526033173857 := by
  unfold tailWord_1644729
  simp only [CollatzResearch.WordTrace]
  refine ⟨59988194858435205194929241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39992129905623470129952827 59988194858435205194929241)
  ·
    refine ⟨44991146143826403896196931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59988194858435205194929241 44991146143826403896196931)
    ·
      refine ⟨67486719215739605844295397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44991146143826403896196931 67486719215739605844295397)
      ·
        refine ⟨12653759852951176095805387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67486719215739605844295397 12653759852951176095805387)
        ·
          refine ⟨18980639779426764143708081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12653759852951176095805387 18980639779426764143708081)
          ·
            refine ⟨14235479834570073107781061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18980639779426764143708081 14235479834570073107781061)
            ·
              refine ⟨2669152468981888707708949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14235479834570073107781061 2669152468981888707708949)
              ·
                refine ⟨125116521983526033173857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2669152468981888707708949 125116521983526033173857)
                ·
                  rfl

theorem cell21_1644729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 6].length) (baseStart_1644729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1644729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1644729 prefixEnd_1644729 := by exact prefixLift 1644729
  have htrace : WordTrace (prefixWord ++ tailWord_1644729) baseStart_1644729 baseEnd_1644729 := by
    simpa [prefixWord, tailWord_1644729, baseEnd_1644729] using wordTrace_append hprefix tailTrace_1644729
  have hstable : (prefixWord ++ tailWord_1644729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644729).length < 2 ^ (prefixWord ++ tailWord_1644729).sum := by decide
  have hdescent : baseEnd_1644729 < baseStart_1644729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644732 : List Nat := [2, 2, 2, 3, 3, 1, 1, 3, 4]
def baseStart_1644732 : Nat := 118140960795 + 1644732 * 2 ^ 59
def prefixEnd_1644732 : Nat := 4983230072969 + 3 ^ 40 * 1644732 * 2
def baseEnd_1644732 : Nat := 375350250591450760971565

theorem tailTrace_1644732 : CollatzResearch.WordTrace tailWord_1644732 prefixEnd_1644732 375350250591450760971565 := by
  unfold tailWord_1644732
  simp only [CollatzResearch.WordTrace]
  refine ⟨29994152138712168353644225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39992202851616224471525633 29994152138712168353644225)
  ·
    refine ⟨22495614104034126265233169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29994152138712168353644225 22495614104034126265233169)
    ·
      refine ⟨16871710578025594698924877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22495614104034126265233169 16871710578025594698924877)
      ·
        refine ⟨6326891466759598012096829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16871710578025594698924877 6326891466759598012096829)
        ·
          refine ⟨2372584300034849254536311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6326891466759598012096829 2372584300034849254536311)
          ·
            refine ⟨3558876450052273881804467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2372584300034849254536311 3558876450052273881804467)
            ·
              refine ⟨5338314675078410822706701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3558876450052273881804467 5338314675078410822706701)
              ·
                refine ⟨2001868003154404058515013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5338314675078410822706701 2001868003154404058515013)
                ·
                  refine ⟨375350250591450760971565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2001868003154404058515013 375350250591450760971565)
                  ·
                    rfl

theorem cell21_1644732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_1644732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1644732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1644732 prefixEnd_1644732 := by exact prefixLift 1644732
  have htrace : WordTrace (prefixWord ++ tailWord_1644732) baseStart_1644732 baseEnd_1644732 := by
    simpa [prefixWord, tailWord_1644732, baseEnd_1644732] using wordTrace_append hprefix tailTrace_1644732
  have hstable : (prefixWord ++ tailWord_1644732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644732).length < 2 ^ (prefixWord ++ tailWord_1644732).sum := by decide
  have hdescent : baseEnd_1644732 < baseStart_1644732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644836 : List Nat := [2, 3, 1, 3, 1, 2, 1, 3, 5]
def baseStart_1644836 : Nat := 118140960795 + 1644836 * 2 ^ 59
def prefixEnd_1644836 : Nat := 4983230072969 + 3 ^ 40 * 1644836 * 2
def baseEnd_1644836 : Nat := 375373984808369691238019

theorem tailTrace_1644836 : CollatzResearch.WordTrace tailWord_1644836 prefixEnd_1644836 375373984808369691238019 := by
  unfold tailWord_1644836
  simp only [CollatzResearch.WordTrace]
  refine ⟨29996048734523781234537181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39994731646031708312716241 29996048734523781234537181)
  ·
    refine ⟨11248518275446417962951443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29996048734523781234537181 11248518275446417962951443)
    ·
      refine ⟨16872777413169626944427165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11248518275446417962951443 16872777413169626944427165)
      ·
        refine ⟨6327291529938610104160187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16872777413169626944427165 6327291529938610104160187)
        ·
          refine ⟨9490937294907915156240281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6327291529938610104160187 9490937294907915156240281)
          ·
            refine ⟨7118202971180936367180211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9490937294907915156240281 7118202971180936367180211)
            ·
              refine ⟨10677304456771404550770317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7118202971180936367180211 10677304456771404550770317)
              ·
                refine ⟨4003989171289276706538869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10677304456771404550770317 4003989171289276706538869)
                ·
                  refine ⟨375373984808369691238019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4003989171289276706538869 375373984808369691238019)
                  ·
                    rfl

theorem cell21_1644836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_1644836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1644836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1644836 prefixEnd_1644836 := by exact prefixLift 1644836
  have htrace : WordTrace (prefixWord ++ tailWord_1644836) baseStart_1644836 baseEnd_1644836 := by
    simpa [prefixWord, tailWord_1644836, baseEnd_1644836] using wordTrace_append hprefix tailTrace_1644836
  have hstable : (prefixWord ++ tailWord_1644836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644836).length < 2 ^ (prefixWord ++ tailWord_1644836).sum := by decide
  have hdescent : baseEnd_1644836 < baseStart_1644836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644881 : List Nat := [1, 2, 2, 1, 4, 4, 7]
def baseStart_1644881 : Nat := 118140960795 + 1644881 * 2 ^ 59
def prefixEnd_1644881 : Nat := 4983230072969 + 3 ^ 40 * 1644881 * 2
def baseEnd_1644881 : Nat := 41709361602384401443103

theorem tailTrace_1644881 : CollatzResearch.WordTrace tailWord_1644881 prefixEnd_1644881 41709361602384401443103 := by
  unfold tailWord_1644881
  simp only [CollatzResearch.WordTrace]
  refine ⟨59993738753884535154462497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39995825835923023436308331 59993738753884535154462497)
  ·
    refine ⟨44995304065413401365846873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59993738753884535154462497 44995304065413401365846873)
    ·
      refine ⟨33746478049060051024385155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44995304065413401365846873 33746478049060051024385155)
      ·
        refine ⟨50619717073590076536577733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33746478049060051024385155 50619717073590076536577733)
        ·
          refine ⟨9491196951298139350608325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50619717073590076536577733 9491196951298139350608325)
          ·
            refine ⟨1779599428368401128239061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9491196951298139350608325 1779599428368401128239061)
            ·
              refine ⟨41709361602384401443103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1779599428368401128239061 41709361602384401443103)
              ·
                rfl

theorem cell21_1644881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 7].length) (baseStart_1644881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1644881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1644881 prefixEnd_1644881 := by exact prefixLift 1644881
  have htrace : WordTrace (prefixWord ++ tailWord_1644881) baseStart_1644881 baseEnd_1644881 := by
    simpa [prefixWord, tailWord_1644881, baseEnd_1644881] using wordTrace_append hprefix tailTrace_1644881
  have hstable : (prefixWord ++ tailWord_1644881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644881).length < 2 ^ (prefixWord ++ tailWord_1644881).sum := by decide
  have hdescent : baseEnd_1644881 < baseStart_1644881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644898 : List Nat := [3, 3, 2, 1, 1, 3, 2, 6]
def baseStart_1644898 : Nat := 118140960795 + 1644898 * 2 ^ 59
def prefixEnd_1644898 : Nat := 4983230072969 + 3 ^ 40 * 1644898 * 2
def baseEnd_1644898 : Nat := 125129378017690453734853

theorem tailTrace_1644898 : CollatzResearch.WordTrace tailWord_1644898 prefixEnd_1644898 125129378017690453734853 := by
  unfold tailWord_1644898
  simp only [CollatzResearch.WordTrace]
  refine ⟨14998589698705736764457837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39996239196548631371887565 14998589698705736764457837)
  ·
    refine ⟨5624471137014651286671689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14998589698705736764457837 5624471137014651286671689)
    ·
      refine ⟨4218353352760988465003767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5624471137014651286671689 4218353352760988465003767)
      ·
        refine ⟨6327530029141482697505651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4218353352760988465003767 6327530029141482697505651)
        ·
          refine ⟨9491295043712224046258477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6327530029141482697505651 9491295043712224046258477)
          ·
            refine ⟨3559235641392084017346929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9491295043712224046258477 3559235641392084017346929)
            ·
              refine ⟨2669426731044063013010197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3559235641392084017346929 2669426731044063013010197)
              ·
                refine ⟨125129378017690453734853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2669426731044063013010197 125129378017690453734853)
                ·
                  rfl

theorem cell21_1644898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 6].length) (baseStart_1644898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1644898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1644898 prefixEnd_1644898 := by exact prefixLift 1644898
  have htrace : WordTrace (prefixWord ++ tailWord_1644898) baseStart_1644898 baseEnd_1644898 := by
    simpa [prefixWord, tailWord_1644898, baseEnd_1644898] using wordTrace_append hprefix tailTrace_1644898
  have hstable : (prefixWord ++ tailWord_1644898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644898).length < 2 ^ (prefixWord ++ tailWord_1644898).sum := by decide
  have hdescent : baseEnd_1644898 < baseStart_1644898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644940 : List Nat := [2, 2, 1, 2, 1, 13]
def baseStart_1644940 : Nat := 118140960795 + 1644940 * 2 ^ 59
def prefixEnd_1644940 : Nat := 4983230072969 + 3 ^ 40 * 1644940 * 2
def baseEnd_1644940 : Nat := 13903619223158837833499

theorem tailTrace_1644940 : CollatzResearch.WordTrace tailWord_1644940 prefixEnd_1644940 13903619223158837833499 := by
  unfold tailWord_1644940
  simp only [CollatzResearch.WordTrace]
  refine ⟨29997945330335394115430137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39997260440447192153906849 29997945330335394115430137)
  ·
    refine ⟨22498458997751545586572603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29997945330335394115430137 22498458997751545586572603)
    ·
      refine ⟨33747688496627318379858905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22498458997751545586572603 33747688496627318379858905)
      ·
        refine ⟨25310766372470488784894179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33747688496627318379858905 25310766372470488784894179)
        ·
          refine ⟨37966149558705733177341269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25310766372470488784894179 37966149558705733177341269)
          ·
            refine ⟨13903619223158837833499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 37966149558705733177341269 13903619223158837833499)
            ·
              rfl

theorem cell21_1644940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 13].length) (baseStart_1644940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1644940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1644940 prefixEnd_1644940 := by exact prefixLift 1644940
  have htrace : WordTrace (prefixWord ++ tailWord_1644940) baseStart_1644940 baseEnd_1644940 := by
    simpa [prefixWord, tailWord_1644940, baseEnd_1644940] using wordTrace_append hprefix tailTrace_1644940
  have hstable : (prefixWord ++ tailWord_1644940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644940).length < 2 ^ (prefixWord ++ tailWord_1644940).sum := by decide
  have hdescent : baseEnd_1644940 < baseStart_1644940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644980 : List Nat := [2, 5, 2, 2, 1, 1, 2, 3, 3]
def baseStart_1644980 : Nat := 118140960795 + 1644980 * 2 ^ 59
def prefixEnd_1644980 : Nat := 4983230072969 + 3 ^ 40 * 1644980 * 2
def baseEnd_1644980 : Nat := 375406847570257440837725

theorem tailTrace_1644980 : CollatzResearch.WordTrace tailWord_1644980 prefixEnd_1644980 375406847570257440837725 := by
  unfold tailWord_1644980
  simp only [CollatzResearch.WordTrace]
  refine ⟨29998674790262937531158197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39998233053683916708210929 29998674790262937531158197)
  ·
    refine ⟨2812375761587150393546081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29998674790262937531158197 2812375761587150393546081)
    ·
      refine ⟨2109281821190362795159561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2812375761587150393546081 2109281821190362795159561)
      ·
        refine ⟨1581961365892772096369671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2109281821190362795159561 1581961365892772096369671)
        ·
          refine ⟨2372942048839158144554507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1581961365892772096369671 2372942048839158144554507)
          ·
            refine ⟨3559413073258737216831761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2372942048839158144554507 3559413073258737216831761)
            ·
              refine ⟨2669559804944052912623821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3559413073258737216831761 2669559804944052912623821)
              ·
                refine ⟨1001084926854019842233933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2669559804944052912623821 1001084926854019842233933)
                ·
                  refine ⟨375406847570257440837725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1001084926854019842233933 375406847570257440837725)
                  ·
                    rfl

theorem cell21_1644980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_1644980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1644980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1644980 prefixEnd_1644980 := by exact prefixLift 1644980
  have htrace : WordTrace (prefixWord ++ tailWord_1644980) baseStart_1644980 baseEnd_1644980 := by
    simpa [prefixWord, tailWord_1644980, baseEnd_1644980] using wordTrace_append hprefix tailTrace_1644980
  have hstable : (prefixWord ++ tailWord_1644980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644980).length < 2 ^ (prefixWord ++ tailWord_1644980).sum := by decide
  have hdescent : baseEnd_1644980 < baseStart_1644980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645002 : List Nat := [3, 1, 2, 1, 2, 2, 3, 1, 6]
def baseStart_1645002 : Nat := 118140960795 + 1645002 * 2 ^ 59
def prefixEnd_1645002 : Nat := 4983230072969 + 3 ^ 40 * 1645002 * 2
def baseEnd_1645002 : Nat := 375411868269990291471013

theorem tailTrace_1645002 : CollatzResearch.WordTrace tailWord_1645002 prefixEnd_1645002 375411868269990291471013 := by
  unfold tailWord_1645002
  simp only [CollatzResearch.WordTrace]
  refine ⟨14999537996611543204904315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39998767990964115213078173 14999537996611543204904315)
  ·
    refine ⟨22499306994917314807356473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14999537996611543204904315 22499306994917314807356473)
    ·
      refine ⟨16874480246187986105517355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22499306994917314807356473 16874480246187986105517355)
      ·
        refine ⟨25311720369281979158276033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16874480246187986105517355 25311720369281979158276033)
        ·
          refine ⟨18983790276961484368707025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25311720369281979158276033 18983790276961484368707025)
          ·
            refine ⟨14237842707721113276530269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18983790276961484368707025 14237842707721113276530269)
            ·
              refine ⟨5339191015395417478698851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14237842707721113276530269 5339191015395417478698851)
              ·
                refine ⟨8008786523093126218048277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5339191015395417478698851 8008786523093126218048277)
                ·
                  refine ⟨375411868269990291471013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8008786523093126218048277 375411868269990291471013)
                  ·
                    rfl

theorem cell21_1645002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_1645002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1645002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1645002 prefixEnd_1645002 := by exact prefixLift 1645002
  have htrace : WordTrace (prefixWord ++ tailWord_1645002) baseStart_1645002 baseEnd_1645002 := by
    simpa [prefixWord, tailWord_1645002, baseEnd_1645002] using wordTrace_append hprefix tailTrace_1645002
  have hstable : (prefixWord ++ tailWord_1645002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645002).length < 2 ^ (prefixWord ++ tailWord_1645002).sum := by decide
  have hdescent : baseEnd_1645002 < baseStart_1645002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645016 : List Nat := [2, 1, 2, 2, 2, 1, 1, 10]
def baseStart_1645016 : Nat := 118140960795 + 1645016 * 2 ^ 59
def prefixEnd_1645016 : Nat := 4983230072969 + 3 ^ 40 * 1645016 * 2
def baseEnd_1645016 : Nat := 125138354420243126079217

theorem tailTrace_1645016 : CollatzResearch.WordTrace tailWord_1645016 prefixEnd_1645016 125138354420243126079217 := by
  unfold tailWord_1645016
  simp only [CollatzResearch.WordTrace]
  refine ⟨29999331304197726605313451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39999108405596968807084601 29999331304197726605313451)
  ·
    refine ⟨44998996956296589907970177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29999331304197726605313451 44998996956296589907970177)
    ·
      refine ⟨33749247717222442430977633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44998996956296589907970177 33749247717222442430977633)
      ·
        refine ⟨25311935787916831823233225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33749247717222442430977633 25311935787916831823233225)
        ·
          refine ⟨18983951840937623867424919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25311935787916831823233225 18983951840937623867424919)
          ·
            refine ⟨28475927761406435801137379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18983951840937623867424919 28475927761406435801137379)
            ·
              refine ⟨42713891642109653701706069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28475927761406435801137379 42713891642109653701706069)
              ·
                refine ⟨125138354420243126079217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42713891642109653701706069 125138354420243126079217)
                ·
                  rfl

theorem cell21_1645016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 10].length) (baseStart_1645016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1645016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1645016 prefixEnd_1645016 := by exact prefixLift 1645016
  have htrace : WordTrace (prefixWord ++ tailWord_1645016) baseStart_1645016 baseEnd_1645016 := by
    simpa [prefixWord, tailWord_1645016, baseEnd_1645016] using wordTrace_append hprefix tailTrace_1645016
  have hstable : (prefixWord ++ tailWord_1645016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645016).length < 2 ^ (prefixWord ++ tailWord_1645016).sum := by decide
  have hdescent : baseEnd_1645016 < baseStart_1645016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645140 : List Nat := [2, 4, 1, 1, 1, 4, 1, 2, 5]
def baseStart_1645140 : Nat := 118140960795 + 1645140 * 2 ^ 59
def prefixEnd_1645140 : Nat := 4983230072969 + 3 ^ 40 * 1645140 * 2
def baseEnd_1645140 : Nat := 375443361750132718170731

theorem tailTrace_1645140 : CollatzResearch.WordTrace tailWord_1645140 prefixEnd_1645140 375443361750132718170731 := by
  unfold tailWord_1645140
  simp only [CollatzResearch.WordTrace]
  refine ⟨30001592629973111194070437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40002123506630814925427249 30001592629973111194070437)
  ·
    refine ⟨5625298618119958348888207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30001592629973111194070437 5625298618119958348888207)
    ·
      refine ⟨8437947927179937523332311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5625298618119958348888207 8437947927179937523332311)
      ·
        refine ⟨12656921890769906284998467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8437947927179937523332311 12656921890769906284998467)
        ·
          refine ⟨18985382836154859427497701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12656921890769906284998467 18985382836154859427497701)
          ·
            refine ⟨3559759281779036142655819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18985382836154859427497701 3559759281779036142655819)
            ·
              refine ⟨5339638922668554213983729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3559759281779036142655819 5339638922668554213983729)
              ·
                refine ⟨4004729192001415660487797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5339638922668554213983729 4004729192001415660487797)
                ·
                  refine ⟨375443361750132718170731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4004729192001415660487797 375443361750132718170731)
                  ·
                    rfl

theorem cell21_1645140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_1645140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1645140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1645140 prefixEnd_1645140 := by exact prefixLift 1645140
  have htrace : WordTrace (prefixWord ++ tailWord_1645140) baseStart_1645140 baseEnd_1645140 := by
    simpa [prefixWord, tailWord_1645140, baseEnd_1645140] using wordTrace_append hprefix tailTrace_1645140
  have hstable : (prefixWord ++ tailWord_1645140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645140).length < 2 ^ (prefixWord ++ tailWord_1645140).sum := by decide
  have hdescent : baseEnd_1645140 < baseStart_1645140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645188 : List Nat := [2, 3, 2, 1, 3, 2, 3, 1, 4]
def baseStart_1645188 : Nat := 118140960795 + 1645188 * 2 ^ 59
def prefixEnd_1645188 : Nat := 4983230072969 + 3 ^ 40 * 1645188 * 2
def baseEnd_1645188 : Nat := 375454316004095301370633

theorem tailTrace_1645188 : CollatzResearch.WordTrace tailWord_1645188 prefixEnd_1645188 375454316004095301370633 := by
  unfold tailWord_1645188
  simp only [CollatzResearch.WordTrace]
  refine ⟨30002467981886163292944109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40003290642514884390592145 30002467981886163292944109)
  ·
    refine ⟨11250925493207311234854041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30002467981886163292944109 11250925493207311234854041)
    ·
      refine ⟨8438194119905483426140531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11250925493207311234854041 8438194119905483426140531)
      ·
        refine ⟨12657291179858225139210797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8438194119905483426140531 12657291179858225139210797)
        ·
          refine ⟨4746484192446834427204049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12657291179858225139210797 4746484192446834427204049)
          ·
            refine ⟨3559863144335125820403037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4746484192446834427204049 3559863144335125820403037)
            ·
              refine ⟨1334948679125672182651139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3559863144335125820403037 1334948679125672182651139)
              ·
                refine ⟨2002423018688508273976709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1334948679125672182651139 2002423018688508273976709)
                ·
                  refine ⟨375454316004095301370633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2002423018688508273976709 375454316004095301370633)
                  ·
                    rfl

theorem cell21_1645188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_1645188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1645188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1645188 prefixEnd_1645188 := by exact prefixLift 1645188
  have htrace : WordTrace (prefixWord ++ tailWord_1645188) baseStart_1645188 baseEnd_1645188 := by
    simpa [prefixWord, tailWord_1645188, baseEnd_1645188] using wordTrace_append hprefix tailTrace_1645188
  have hstable : (prefixWord ++ tailWord_1645188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645188).length < 2 ^ (prefixWord ++ tailWord_1645188).sum := by decide
  have hdescent : baseEnd_1645188 < baseStart_1645188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645202 : List Nat := [3, 2, 3, 1, 2, 1, 4, 5]
def baseStart_1645202 : Nat := 118140960795 + 1645202 * 2 ^ 59
def prefixEnd_1645202 : Nat := 4983230072969 + 3 ^ 40 * 1645202 * 2
def baseEnd_1645202 : Nat := 125152503664944796045757

theorem tailTrace_1645202 : CollatzResearch.WordTrace tailWord_1645202 prefixEnd_1645202 125152503664944796045757 := by
  unfold tailWord_1645202
  simp only [CollatzResearch.WordTrace]
  refine ⟨15001361646430401744224465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40003631057147737984598573 15001361646430401744224465)
  ·
    refine ⟨11251021234822801308168349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15001361646430401744224465 11251021234822801308168349)
    ·
      refine ⟨4219132963058550490563131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11251021234822801308168349 4219132963058550490563131)
      ·
        refine ⟨6328699444587825735844697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4219132963058550490563131 6328699444587825735844697)
        ·
          refine ⟨4746524583440869301883523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6328699444587825735844697 4746524583440869301883523)
          ·
            refine ⟨7119786875161303952825285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4746524583440869301883523 7119786875161303952825285)
            ·
              refine ⟨1334960039092744491154741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7119786875161303952825285 1334960039092744491154741)
              ·
                refine ⟨125152503664944796045757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1334960039092744491154741 125152503664944796045757)
                ·
                  rfl

theorem cell21_1645202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 5].length) (baseStart_1645202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1645202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1645202 prefixEnd_1645202 := by exact prefixLift 1645202
  have htrace : WordTrace (prefixWord ++ tailWord_1645202) baseStart_1645202 baseEnd_1645202 := by
    simpa [prefixWord, tailWord_1645202, baseEnd_1645202] using wordTrace_append hprefix tailTrace_1645202
  have hstable : (prefixWord ++ tailWord_1645202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645202).length < 2 ^ (prefixWord ++ tailWord_1645202).sum := by decide
  have hdescent : baseEnd_1645202 < baseStart_1645202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645247 : List Nat := [1, 1, 2, 2, 2, 4, 4, 1, 4]
def baseStart_1645247 : Nat := 118140960795 + 1645247 * 2 ^ 59
def prefixEnd_1645247 : Nat := 4983230072969 + 3 ^ 40 * 1645247 * 2
def baseEnd_1645247 : Nat := 375467780607924309887179

theorem tailTrace_1645247 : CollatzResearch.WordTrace tailWord_1645247 prefixEnd_1645247 375467780607924309887179 := by
  unfold tailWord_1645247
  simp only [CollatzResearch.WordTrace]
  refine ⟨60007087870558579662285995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40004725247039053108190663 60007087870558579662285995)
  ·
    refine ⟨90010631805837869493428993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60007087870558579662285995 90010631805837869493428993)
    ·
      refine ⟨67507973854378402120071745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90010631805837869493428993 67507973854378402120071745)
      ·
        refine ⟨50630980390783801590053809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67507973854378402120071745 50630980390783801590053809)
        ·
          refine ⟨37973235293087851192540357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50630980390783801590053809 37973235293087851192540357)
          ·
            refine ⟨7119981617453972098601317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37973235293087851192540357 7119981617453972098601317)
            ·
              refine ⟨1334996553272619768487747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7119981617453972098601317 1334996553272619768487747)
              ·
                refine ⟨2002494829908929652731621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1334996553272619768487747 2002494829908929652731621)
                ·
                  refine ⟨375467780607924309887179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2002494829908929652731621 375467780607924309887179)
                  ·
                    rfl

theorem cell21_1645247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 4].length) (baseStart_1645247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1645247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1645247 prefixEnd_1645247 := by exact prefixLift 1645247
  have htrace : WordTrace (prefixWord ++ tailWord_1645247) baseStart_1645247 baseEnd_1645247 := by
    simpa [prefixWord, tailWord_1645247, baseEnd_1645247] using wordTrace_append hprefix tailTrace_1645247
  have hstable : (prefixWord ++ tailWord_1645247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645247).length < 2 ^ (prefixWord ++ tailWord_1645247).sum := by decide
  have hdescent : baseEnd_1645247 < baseStart_1645247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645289 : List Nat := [1, 2, 1, 1, 1, 2, 4, 3, 6]
def baseStart_1645289 : Nat := 118140960795 + 1645289 * 2 ^ 59
def prefixEnd_1645289 : Nat := 4983230072969 + 3 ^ 40 * 1645289 * 2
def baseEnd_1645289 : Nat := 375477365580141570187093

theorem tailTrace_1645289 : CollatzResearch.WordTrace tailWord_1645289 prefixEnd_1645289 375477365580141570187093 := by
  unfold tailWord_1645289
  simp only [CollatzResearch.WordTrace]
  refine ⟨60008619736406420835314921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40005746490937613890209947 60008619736406420835314921)
  ·
    refine ⟨45006464802304815626486191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60008619736406420835314921 45006464802304815626486191)
    ·
      refine ⟨67509697203457223439729287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45006464802304815626486191 67509697203457223439729287)
      ·
        refine ⟨101264545805185835159593931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67509697203457223439729287 101264545805185835159593931)
        ·
          refine ⟨151896818707778752739390897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101264545805185835159593931 151896818707778752739390897)
          ·
            refine ⟨113922614030834064554543173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151896818707778752739390897 113922614030834064554543173)
            ·
              refine ⟨21360490130781387103976845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113922614030834064554543173 21360490130781387103976845)
              ·
                refine ⟨8010183799043020163991317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21360490130781387103976845 8010183799043020163991317)
                ·
                  refine ⟨375477365580141570187093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8010183799043020163991317 375477365580141570187093)
                  ·
                    rfl

theorem cell21_1645289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 6].length) (baseStart_1645289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1645289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1645289 prefixEnd_1645289 := by exact prefixLift 1645289
  have htrace : WordTrace (prefixWord ++ tailWord_1645289) baseStart_1645289 baseEnd_1645289 := by
    simpa [prefixWord, tailWord_1645289, baseEnd_1645289] using wordTrace_append hprefix tailTrace_1645289
  have hstable : (prefixWord ++ tailWord_1645289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645289).length < 2 ^ (prefixWord ++ tailWord_1645289).sum := by decide
  have hdescent : baseEnd_1645289 < baseStart_1645289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645306 : List Nat := [3, 1, 1, 1, 1, 3, 4, 3, 4]
def baseStart_1645306 : Nat := 118140960795 + 1645306 * 2 ^ 59
def prefixEnd_1645306 : Nat := 4983230072969 + 3 ^ 40 * 1645306 * 2
def baseEnd_1645306 : Nat := 375481245211753318403725

theorem tailTrace_1645306 : CollatzResearch.WordTrace tailWord_1645306 prefixEnd_1645306 375481245211753318403725 := by
  unfold tailWord_1645306
  simp only [CollatzResearch.WordTrace]
  refine ⟨15002309944336208184670943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40006159851563221825789181 15002309944336208184670943)
  ·
    refine ⟨22503464916504312277006415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15002309944336208184670943 22503464916504312277006415)
    ·
      refine ⟨33755197374756468415509623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22503464916504312277006415 33755197374756468415509623)
      ·
        refine ⟨50632796062134702623264435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33755197374756468415509623 50632796062134702623264435)
        ·
          refine ⟨75949194093202053934896653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50632796062134702623264435 75949194093202053934896653)
          ·
            refine ⟨28480947784950770225586245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75949194093202053934896653 28480947784950770225586245)
            ·
              refine ⟨5340177709678269417297421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28480947784950770225586245 5340177709678269417297421)
              ·
                refine ⟨2002566641129351031486533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5340177709678269417297421 2002566641129351031486533)
                ·
                  refine ⟨375481245211753318403725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2002566641129351031486533 375481245211753318403725)
                  ·
                    rfl

theorem cell21_1645306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_1645306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1645306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1645306 prefixEnd_1645306 := by exact prefixLift 1645306
  have htrace : WordTrace (prefixWord ++ tailWord_1645306) baseStart_1645306 baseEnd_1645306 := by
    simpa [prefixWord, tailWord_1645306, baseEnd_1645306] using wordTrace_append hprefix tailTrace_1645306
  have hstable : (prefixWord ++ tailWord_1645306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645306).length < 2 ^ (prefixWord ++ tailWord_1645306).sum := by decide
  have hdescent : baseEnd_1645306 < baseStart_1645306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645385 : List Nat := [1, 2, 1, 1, 2, 7, 1, 3, 3]
def baseStart_1645385 : Nat := 118140960795 + 1645385 * 2 ^ 59
def prefixEnd_1645385 : Nat := 4983230072969 + 3 ^ 40 * 1645385 * 2
def baseEnd_1645385 : Nat := 375499274088066736586897

theorem tailTrace_1645385 : CollatzResearch.WordTrace tailWord_1645385 prefixEnd_1645385 375499274088066736586897 := by
  unfold tailWord_1645385
  simp only [CollatzResearch.WordTrace]
  refine ⟨60012121144058629230809609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40008080762705752820539739 60012121144058629230809609)
  ·
    refine ⟨45009090858043971923107207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60012121144058629230809609 45009090858043971923107207)
    ·
      refine ⟨67513636287065957884660811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45009090858043971923107207 67513636287065957884660811)
      ·
        refine ⟨101270454430598936826991217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67513636287065957884660811 101270454430598936826991217)
        ·
          refine ⟨75952840822949202620243413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101270454430598936826991217 75952840822949202620243413)
          ·
            refine ⟨1780144706787871936411955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 75952840822949202620243413 1780144706787871936411955)
            ·
              refine ⟨2670217060181807904617933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1780144706787871936411955 2670217060181807904617933)
              ·
                refine ⟨1001331397568177964231725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2670217060181807904617933 1001331397568177964231725)
                ·
                  refine ⟨375499274088066736586897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1001331397568177964231725 375499274088066736586897)
                  ·
                    rfl

theorem cell21_1645385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3, 3].length) (baseStart_1645385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1645385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1645385 prefixEnd_1645385 := by exact prefixLift 1645385
  have htrace : WordTrace (prefixWord ++ tailWord_1645385) baseStart_1645385 baseEnd_1645385 := by
    simpa [prefixWord, tailWord_1645385, baseEnd_1645385] using wordTrace_append hprefix tailTrace_1645385
  have hstable : (prefixWord ++ tailWord_1645385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645385).length < 2 ^ (prefixWord ++ tailWord_1645385).sum := by decide
  have hdescent : baseEnd_1645385 < baseStart_1645385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645416 : List Nat := [2, 1, 4, 2, 1, 4, 2, 1, 4]
def baseStart_1645416 : Nat := 118140960795 + 1645416 * 2 ^ 59
def prefixEnd_1645416 : Nat := 4983230072969 + 3 ^ 40 * 1645416 * 2
def baseEnd_1645416 : Nat := 375506348710417571570167

theorem tailTrace_1645416 : CollatzResearch.WordTrace tailWord_1645416 prefixEnd_1645416 375506348710417571570167 := by
  unfold tailWord_1645416
  simp only [CollatzResearch.WordTrace]
  refine ⟨30006625903473160762594051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40008834537964214350125401 30006625903473160762594051)
  ·
    refine ⟨45009938855209741143891077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30006625903473160762594051 45009938855209741143891077)
    ·
      refine ⟨8439363535351826464479577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45009938855209741143891077 8439363535351826464479577)
      ·
        refine ⟨6329522651513869848359683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8439363535351826464479577 6329522651513869848359683)
        ·
          refine ⟨9494283977270804772539525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6329522651513869848359683 9494283977270804772539525)
          ·
            refine ⟨1780178245738275894851161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9494283977270804772539525 1780178245738275894851161)
            ·
              refine ⟨1335133684303706921138371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1780178245738275894851161 1335133684303706921138371)
              ·
                refine ⟨2002700526455560381707557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335133684303706921138371 2002700526455560381707557)
                ·
                  refine ⟨375506348710417571570167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2002700526455560381707557 375506348710417571570167)
                  ·
                    rfl

theorem cell21_1645416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 4].length) (baseStart_1645416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1645416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1645416 prefixEnd_1645416 := by exact prefixLift 1645416
  have htrace : WordTrace (prefixWord ++ tailWord_1645416) baseStart_1645416 baseEnd_1645416 := by
    simpa [prefixWord, tailWord_1645416, baseEnd_1645416] using wordTrace_append hprefix tailTrace_1645416
  have hstable : (prefixWord ++ tailWord_1645416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645416).length < 2 ^ (prefixWord ++ tailWord_1645416).sum := by decide
  have hdescent : baseEnd_1645416 < baseStart_1645416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645444 : List Nat := [2, 3, 2, 1, 1, 1, 1, 7, 3]
def baseStart_1645444 : Nat := 118140960795 + 1645444 * 2 ^ 59
def prefixEnd_1645444 : Nat := 4983230072969 + 3 ^ 40 * 1645444 * 2
def baseEnd_1645444 : Nat := 375512738691895745103443

theorem tailTrace_1645444 : CollatzResearch.WordTrace tailWord_1645444 prefixEnd_1645444 375512738691895745103443 := by
  unfold tailWord_1645444
  simp only [CollatzResearch.WordTrace]
  refine ⟨30007136525422441153603693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40009515367229921538138257 30007136525422441153603693)
  ·
    refine ⟨11252676197033415432601385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30007136525422441153603693 11252676197033415432601385)
    ·
      refine ⟨8439507147775061574451039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11252676197033415432601385 8439507147775061574451039)
      ·
        refine ⟨12659260721662592361676559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8439507147775061574451039 12659260721662592361676559)
        ·
          refine ⟨18988891082493888542514839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12659260721662592361676559 18988891082493888542514839)
          ·
            refine ⟨28483336623740832813772259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18988891082493888542514839 28483336623740832813772259)
            ·
              refine ⟨42725004935611249220658389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28483336623740832813772259 42725004935611249220658389)
              ·
                refine ⟨1001367303178388653609181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 42725004935611249220658389 1001367303178388653609181)
                ·
                  refine ⟨375512738691895745103443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1001367303178388653609181 375512738691895745103443)
                  ·
                    rfl

theorem cell21_1645444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_1645444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1645444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1645444 prefixEnd_1645444 := by exact prefixLift 1645444
  have htrace : WordTrace (prefixWord ++ tailWord_1645444) baseStart_1645444 baseEnd_1645444 := by
    simpa [prefixWord, tailWord_1645444, baseEnd_1645444] using wordTrace_append hprefix tailTrace_1645444
  have hstable : (prefixWord ++ tailWord_1645444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645444).length < 2 ^ (prefixWord ++ tailWord_1645444).sum := by decide
  have hdescent : baseEnd_1645444 < baseStart_1645444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645461 : List Nat := [1, 3, 2, 1, 1, 4, 4, 2, 3]
def baseStart_1645461 : Nat := 118140960795 + 1645461 * 2 ^ 59
def prefixEnd_1645461 : Nat := 4983230072969 + 3 ^ 40 * 1645461 * 2
def baseEnd_1645461 : Nat := 375516618323507493320075

theorem tailTrace_1645461 : CollatzResearch.WordTrace tailWord_1645461 prefixEnd_1645461 375516618323507493320075 := by
  unfold tailWord_1645461
  simp only [CollatzResearch.WordTrace]
  refine ⟨60014893091783294210576237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40009928727855529473717491 60014893091783294210576237)
  ·
    refine ⟨22505584909418735328966089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60014893091783294210576237 22505584909418735328966089)
    ·
      refine ⟨16879188682064051496724567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22505584909418735328966089 16879188682064051496724567)
      ·
        refine ⟨25318783023096077245086851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16879188682064051496724567 25318783023096077245086851)
        ·
          refine ⟨37978174534644115867630277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25318783023096077245086851 37978174534644115867630277)
          ·
            refine ⟨7120907725245771725180677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37978174534644115867630277 7120907725245771725180677)
            ·
              refine ⟨1335170198483582198471377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7120907725245771725180677 1335170198483582198471377)
              ·
                refine ⟨1001377648862686648853533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1335170198483582198471377 1001377648862686648853533)
                ·
                  refine ⟨375516618323507493320075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1001377648862686648853533 375516618323507493320075)
                  ·
                    rfl

theorem cell21_1645461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2, 3].length) (baseStart_1645461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1645461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1645461 prefixEnd_1645461 := by exact prefixLift 1645461
  have htrace : WordTrace (prefixWord ++ tailWord_1645461) baseStart_1645461 baseEnd_1645461 := by
    simpa [prefixWord, tailWord_1645461, baseEnd_1645461] using wordTrace_append hprefix tailTrace_1645461
  have hstable : (prefixWord ++ tailWord_1645461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645461).length < 2 ^ (prefixWord ++ tailWord_1645461).sum := by decide
  have hdescent : baseEnd_1645461 < baseStart_1645461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645472 : List Nat := [2, 1, 1, 4, 1, 1, 5, 6]
def baseStart_1645472 : Nat := 118140960795 + 1645472 * 2 ^ 59
def prefixEnd_1645472 : Nat := 4983230072969 + 3 ^ 40 * 1645472 * 2
def baseEnd_1645472 : Nat := 125173042891124639545573

theorem tailTrace_1645472 : CollatzResearch.WordTrace tailWord_1645472 prefixEnd_1645472 125173042891124639545573 := by
  unfold tailWord_1645472
  simp only [CollatzResearch.WordTrace]
  refine ⟨30007647147371721544613335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40010196196495628726151113 30007647147371721544613335)
  ·
    refine ⟨45011470721057582316920003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30007647147371721544613335 45011470721057582316920003)
    ·
      refine ⟨67517206081586373475380005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45011470721057582316920003 67517206081586373475380005)
      ·
        refine ⟨12659476140297445026633751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67517206081586373475380005 12659476140297445026633751)
        ·
          refine ⟨18989214210446167539950627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12659476140297445026633751 18989214210446167539950627)
          ·
            refine ⟨28483821315669251309925941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18989214210446167539950627 28483821315669251309925941)
            ·
              refine ⟨2670358248343992310305557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28483821315669251309925941 2670358248343992310305557)
              ·
                refine ⟨125173042891124639545573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2670358248343992310305557 125173042891124639545573)
                ·
                  rfl

theorem cell21_1645472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 6].length) (baseStart_1645472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1645472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1645472 prefixEnd_1645472 := by exact prefixLift 1645472
  have htrace : WordTrace (prefixWord ++ tailWord_1645472) baseStart_1645472 baseEnd_1645472 := by
    simpa [prefixWord, tailWord_1645472, baseEnd_1645472] using wordTrace_append hprefix tailTrace_1645472
  have hstable : (prefixWord ++ tailWord_1645472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645472).length < 2 ^ (prefixWord ++ tailWord_1645472).sum := by decide
  have hdescent : baseEnd_1645472 < baseStart_1645472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645562 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 7]
def baseStart_1645562 : Nat := 118140960795 + 1645562 * 2 ^ 59
def prefixEnd_1645562 : Nat := 4983230072969 + 3 ^ 40 * 1645562 * 2
def baseEnd_1645562 : Nat := 375539667899553762136535

theorem tailTrace_1645562 : CollatzResearch.WordTrace tailWord_1645562 prefixEnd_1645562 375539667899553762136535 := by
  unfold tailWord_1645562
  simp only [CollatzResearch.WordTrace]
  refine ⟨15004644216104347115000735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40012384576278258973335293 15004644216104347115000735)
  ·
    refine ⟨22506966324156520672501103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15004644216104347115000735 22506966324156520672501103)
    ·
      refine ⟨33760449486234781008751655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22506966324156520672501103 33760449486234781008751655)
      ·
        refine ⟨50640674229352171513127483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33760449486234781008751655 50640674229352171513127483)
        ·
          refine ⟨75961011344028257269691225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50640674229352171513127483 75961011344028257269691225)
          ·
            refine ⟨56970758508021192952268419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75961011344028257269691225 56970758508021192952268419)
            ·
              refine ⟨85456137762031789428402629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56970758508021192952268419 85456137762031789428402629)
              ·
                refine ⟨16023025830380960517825493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85456137762031789428402629 16023025830380960517825493)
                ·
                  refine ⟨375539667899553762136535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16023025830380960517825493 375539667899553762136535)
                  ·
                    rfl

theorem cell21_1645562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_1645562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1645562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1645562 prefixEnd_1645562 := by exact prefixLift 1645562
  have htrace : WordTrace (prefixWord ++ tailWord_1645562) baseStart_1645562 baseEnd_1645562 := by
    simpa [prefixWord, tailWord_1645562, baseEnd_1645562] using wordTrace_append hprefix tailTrace_1645562
  have hstable : (prefixWord ++ tailWord_1645562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645562).length < 2 ^ (prefixWord ++ tailWord_1645562).sum := by decide
  have hdescent : baseEnd_1645562 < baseStart_1645562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645579 : List Nat := [1, 1, 1, 1, 6, 2, 3, 1, 5]
def baseStart_1645579 : Nat := 118140960795 + 1645579 * 2 ^ 59
def prefixEnd_1645579 : Nat := 4983230072969 + 3 ^ 40 * 1645579 * 2
def baseEnd_1645579 : Nat := 375543547531165510353167

theorem tailTrace_1645579 : CollatzResearch.WordTrace tailWord_1645579 prefixEnd_1645579 375543547531165510353167 := by
  unfold tailWord_1645579
  simp only [CollatzResearch.WordTrace]
  refine ⟨60019196905355800363371791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40012797936903866908914527 60019196905355800363371791)
  ·
    refine ⟨90028795358033700545057687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60019196905355800363371791 90028795358033700545057687)
    ·
      refine ⟨135043193037050550817586531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90028795358033700545057687 135043193037050550817586531)
      ·
        refine ⟨202564789555575826226379797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135043193037050550817586531 202564789555575826226379797)
        ·
          refine ⟨9495224510417616854361553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 202564789555575826226379797 9495224510417616854361553)
          ·
            refine ⟨7121418382813212640771165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9495224510417616854361553 7121418382813212640771165)
            ·
              refine ⟨2670531893554954740289187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7121418382813212640771165 2670531893554954740289187)
              ·
                refine ⟨4005797840332432110433781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2670531893554954740289187 4005797840332432110433781)
                ·
                  refine ⟨375543547531165510353167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4005797840332432110433781 375543547531165510353167)
                  ·
                    rfl

theorem cell21_1645579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 5].length) (baseStart_1645579 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1645579 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1645579 prefixEnd_1645579 := by exact prefixLift 1645579
  have htrace : WordTrace (prefixWord ++ tailWord_1645579) baseStart_1645579 baseEnd_1645579 := by
    simpa [prefixWord, tailWord_1645579, baseEnd_1645579] using wordTrace_append hprefix tailTrace_1645579
  have hstable : (prefixWord ++ tailWord_1645579).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645579).length < 2 ^ (prefixWord ++ tailWord_1645579).sum := by decide
  have hdescent : baseEnd_1645579 < baseStart_1645579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645630 : List Nat := [4, 2, 1, 3, 1, 1, 4, 2, 3]
def baseStart_1645630 : Nat := 118140960795 + 1645630 * 2 ^ 59
def prefixEnd_1645630 : Nat := 4983230072969 + 3 ^ 40 * 1645630 * 2
def baseEnd_1645630 : Nat := 375555186426000755003063

theorem tailTrace_1645630 : CollatzResearch.WordTrace tailWord_1645630 prefixEnd_1645630 375555186426000755003063 := by
  unfold tailWord_1645630
  simp only [CollatzResearch.WordTrace]
  refine ⟨7502632128521379509184793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40014038018780690715652229 7502632128521379509184793)
  ·
    refine ⟨5626974096391034631888595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7502632128521379509184793 5626974096391034631888595)
    ·
      refine ⟨8440461144586551947832893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5626974096391034631888595 8440461144586551947832893)
      ·
        refine ⟨3165172929219956980437335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8440461144586551947832893 3165172929219956980437335)
        ·
          refine ⟨4747759393829935470656003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3165172929219956980437335 4747759393829935470656003)
          ·
            refine ⟨7121639090744903205984005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4747759393829935470656003 7121639090744903205984005)
            ·
              refine ⟨1335307329514669351122001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7121639090744903205984005 1335307329514669351122001)
              ·
                refine ⟨1001480497136002013341501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1335307329514669351122001 1001480497136002013341501)
                ·
                  refine ⟨375555186426000755003063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1001480497136002013341501 375555186426000755003063)
                  ·
                    rfl

theorem cell21_1645630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_1645630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1645630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1645630 prefixEnd_1645630 := by exact prefixLift 1645630
  have htrace : WordTrace (prefixWord ++ tailWord_1645630) baseStart_1645630 baseEnd_1645630 := by
    simpa [prefixWord, tailWord_1645630, baseEnd_1645630] using wordTrace_append hprefix tailTrace_1645630
  have hstable : (prefixWord ++ tailWord_1645630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645630).length < 2 ^ (prefixWord ++ tailWord_1645630).sum := by decide
  have hdescent : baseEnd_1645630 < baseStart_1645630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645669 : List Nat := [1, 3, 1, 3, 2, 1, 2, 2, 6]
def baseStart_1645669 : Nat := 118140960795 + 1645669 * 2 ^ 59
def prefixEnd_1645669 : Nat := 4983230072969 + 3 ^ 40 * 1645669 * 2
def baseEnd_1645669 : Nat := 375564086757345353852983

theorem tailTrace_1645669 : CollatzResearch.WordTrace tailWord_1645669 prefixEnd_1645669 375564086757345353852983 := by
  unfold tailWord_1645669
  simp only [CollatzResearch.WordTrace]
  refine ⟨60022479475029745734148061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40014986316686497156098707 60022479475029745734148061)
  ·
    refine ⟨22508429803136154650305523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60022479475029745734148061 22508429803136154650305523)
    ·
      refine ⟨33762644704704231975458285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22508429803136154650305523 33762644704704231975458285)
      ·
        refine ⟨12660991764264086990796857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33762644704704231975458285 12660991764264086990796857)
        ·
          refine ⟨9495743823198065243097643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12660991764264086990796857 9495743823198065243097643)
          ·
            refine ⟨14243615734797097864646465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9495743823198065243097643 14243615734797097864646465)
            ·
              refine ⟨10682711801097823398484849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14243615734797097864646465 10682711801097823398484849)
              ·
                refine ⟨8012033850823367548863637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10682711801097823398484849 8012033850823367548863637)
                ·
                  refine ⟨375564086757345353852983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8012033850823367548863637 375564086757345353852983)
                  ·
                    rfl

theorem cell21_1645669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_1645669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1645669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1645669 prefixEnd_1645669 := by exact prefixLift 1645669
  have htrace : WordTrace (prefixWord ++ tailWord_1645669) baseStart_1645669 baseEnd_1645669 := by
    simpa [prefixWord, tailWord_1645669, baseEnd_1645669] using wordTrace_append hprefix tailTrace_1645669
  have hstable : (prefixWord ++ tailWord_1645669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645669).length < 2 ^ (prefixWord ++ tailWord_1645669).sum := by decide
  have hdescent : baseEnd_1645669 < baseStart_1645669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645686 : List Nat := [5, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_1645686 : Nat := 118140960795 + 1645686 * 2 ^ 59
def prefixEnd_1645686 : Nat := 4983230072969 + 3 ^ 40 * 1645686 * 2
def baseEnd_1645686 : Nat := 375567966388957102069615

theorem tailTrace_1645686 : CollatzResearch.WordTrace tailWord_1645686 prefixEnd_1645686 375567966388957102069615 := by
  unfold tailWord_1645686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3751443719748009852344807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40015399677312105091677941 3751443719748009852344807)
  ·
    refine ⟨5627165579622014778517211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3751443719748009852344807 5627165579622014778517211)
    ·
      refine ⟨8440748369433022167775817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5627165579622014778517211 8440748369433022167775817)
      ·
        refine ⟨6330561277074766625831863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8440748369433022167775817 6330561277074766625831863)
        ·
          refine ⟨9495841915612149938747795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6330561277074766625831863 9495841915612149938747795)
          ·
            refine ⟨14243762873418224908121693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9495841915612149938747795 14243762873418224908121693)
            ·
              refine ⟨5341411077531834340545635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14243762873418224908121693 5341411077531834340545635)
              ·
                refine ⟨8012116616297751510818453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5341411077531834340545635 8012116616297751510818453)
                ·
                  refine ⟨375567966388957102069615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8012116616297751510818453 375567966388957102069615)
                  ·
                    rfl

theorem cell21_1645686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_1645686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1645686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1645686 prefixEnd_1645686 := by exact prefixLift 1645686
  have htrace : WordTrace (prefixWord ++ tailWord_1645686) baseStart_1645686 baseEnd_1645686 := by
    simpa [prefixWord, tailWord_1645686, baseEnd_1645686] using wordTrace_append hprefix tailTrace_1645686
  have hstable : (prefixWord ++ tailWord_1645686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645686).length < 2 ^ (prefixWord ++ tailWord_1645686).sum := by decide
  have hdescent : baseEnd_1645686 < baseStart_1645686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645759 : List Nat := [1, 1, 2, 2, 2, 2, 3, 8]
def baseStart_1645759 : Nat := 118140960795 + 1645759 * 2 ^ 59
def prefixEnd_1645759 : Nat := 4983230072969 + 3 ^ 40 * 1645759 * 2
def baseEnd_1645759 : Nat := 125194875327841732450933

theorem tailTrace_1645759 : CollatzResearch.WordTrace tailWord_1645759 prefixEnd_1645759 125194875327841732450933 := by
  unfold tailWord_1645759
  simp only [CollatzResearch.WordTrace]
  refine ⟨60025762044703691104924331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40017174696469127403282887 60025762044703691104924331)
  ·
    refine ⟨90038643067055536657386497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60025762044703691104924331 90038643067055536657386497)
    ·
      refine ⟨67528982300291652493039873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90038643067055536657386497 67528982300291652493039873)
      ·
        refine ⟨50646736725218739369779905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67528982300291652493039873 50646736725218739369779905)
        ·
          refine ⟨37985052543914054527334929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50646736725218739369779905 37985052543914054527334929)
          ·
            refine ⟨28488789407935540895501197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37985052543914054527334929 28488789407935540895501197)
            ·
              refine ⟨10683296027975827835812949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28488789407935540895501197 10683296027975827835812949)
              ·
                refine ⟨125194875327841732450933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10683296027975827835812949 125194875327841732450933)
                ·
                  rfl

theorem cell21_1645759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 8].length) (baseStart_1645759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1645759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1645759 prefixEnd_1645759 := by exact prefixLift 1645759
  have htrace : WordTrace (prefixWord ++ tailWord_1645759) baseStart_1645759 baseEnd_1645759 := by
    simpa [prefixWord, tailWord_1645759, baseEnd_1645759] using wordTrace_append hprefix tailTrace_1645759
  have hstable : (prefixWord ++ tailWord_1645759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645759).length < 2 ^ (prefixWord ++ tailWord_1645759).sum := by decide
  have hdescent : baseEnd_1645759 < baseStart_1645759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645799 : List Nat := [1, 1, 5, 3, 3, 1, 2, 2, 3]
def baseStart_1645799 : Nat := 118140960795 + 1645799 * 2 ^ 59
def prefixEnd_1645799 : Nat := 4983230072969 + 3 ^ 40 * 1645799 * 2
def baseEnd_1645799 : Nat := 375593754528494016686051

theorem tailTrace_1645799 : CollatzResearch.WordTrace tailWord_1645799 prefixEnd_1645799 375593754528494016686051 := by
  unfold tailWord_1645799
  simp only [CollatzResearch.WordTrace]
  refine ⟨60027220964558777936380451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40018147309705851957586967 60027220964558777936380451)
  ·
    refine ⟨90040831446838166904570677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60027220964558777936380451 90040831446838166904570677)
    ·
      refine ⟨8441327948141078147303501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90040831446838166904570677 8441327948141078147303501)
      ·
        refine ⟨3165497980552904305238813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8441327948141078147303501 3165497980552904305238813)
        ·
          refine ⟨1187061742707339114464555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3165497980552904305238813 1187061742707339114464555)
          ·
            refine ⟨1780592614061008671696833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1187061742707339114464555 1780592614061008671696833)
            ·
              refine ⟨1335444460545756503772625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1780592614061008671696833 1335444460545756503772625)
              ·
                refine ⟨1001583345409317377829469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1335444460545756503772625 1001583345409317377829469)
                ·
                  refine ⟨375593754528494016686051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1001583345409317377829469 375593754528494016686051)
                  ·
                    rfl

theorem cell21_1645799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2, 3].length) (baseStart_1645799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1645799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1645799 prefixEnd_1645799 := by exact prefixLift 1645799
  have htrace : WordTrace (prefixWord ++ tailWord_1645799) baseStart_1645799 baseEnd_1645799 := by
    simpa [prefixWord, tailWord_1645799, baseEnd_1645799] using wordTrace_append hprefix tailTrace_1645799
  have hstable : (prefixWord ++ tailWord_1645799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645799).length < 2 ^ (prefixWord ++ tailWord_1645799).sum := by decide
  have hdescent : baseEnd_1645799 < baseStart_1645799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645810 : List Nat := [3, 2, 1, 3, 4, 1, 1, 6]
def baseStart_1645810 : Nat := 118140960795 + 1645810 * 2 ^ 59
def prefixEnd_1645810 : Nat := 4983230072969 + 3 ^ 40 * 1645810 * 2
def baseEnd_1645810 : Nat := 125198754959453480667565

theorem tailTrace_1645810 : CollatzResearch.WordTrace tailWord_1645810 prefixEnd_1645810 125198754959453480667565 := by
  unfold tailWord_1645810
  simp only [CollatzResearch.WordTrace]
  refine ⟨15006905541879731703757721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40018414778345951210020589 15006905541879731703757721)
  ·
    refine ⟨11255179156409798777818291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15006905541879731703757721 11255179156409798777818291)
    ·
      refine ⟨16882768734614698166727437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11255179156409798777818291 16882768734614698166727437)
      ·
        refine ⟨6331038275480511812522789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16882768734614698166727437 6331038275480511812522789)
        ·
          refine ⟨1187069676652595964848023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6331038275480511812522789 1187069676652595964848023)
          ·
            refine ⟨1780604514978893947272035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1187069676652595964848023 1780604514978893947272035)
            ·
              refine ⟨2670906772468340920908053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1780604514978893947272035 2670906772468340920908053)
              ·
                refine ⟨125198754959453480667565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2670906772468340920908053 125198754959453480667565)
                ·
                  rfl

theorem cell21_1645810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 6].length) (baseStart_1645810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1645810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1645810 prefixEnd_1645810 := by exact prefixLift 1645810
  have htrace : WordTrace (prefixWord ++ tailWord_1645810) baseStart_1645810 baseEnd_1645810 := by
    simpa [prefixWord, tailWord_1645810, baseEnd_1645810] using wordTrace_append hprefix tailTrace_1645810
  have hstable : (prefixWord ++ tailWord_1645810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645810).length < 2 ^ (prefixWord ++ tailWord_1645810).sum := by decide
  have hdescent : baseEnd_1645810 < baseStart_1645810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645855 : List Nat := [1, 1, 2, 4, 4, 2, 1, 2, 4]
def baseStart_1645855 : Nat := 118140960795 + 1645855 * 2 ^ 59
def prefixEnd_1645855 : Nat := 4983230072969 + 3 ^ 40 * 1645855 * 2
def baseEnd_1645855 : Nat := 375606534491450363752603

theorem tailTrace_1645855 : CollatzResearch.WordTrace tailWord_1645855 prefixEnd_1645855 375606534491450363752603 := by
  unfold tailWord_1645855
  simp only [CollatzResearch.WordTrace]
  refine ⟨60029263452355899500419019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40019508968237266333612679 60029263452355899500419019)
  ·
    refine ⟨90043895178533849250628529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60029263452355899500419019 90043895178533849250628529)
    ·
      refine ⟨67532921383900386937971397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90043895178533849250628529 67532921383900386937971397)
      ·
        refine ⟨12662422759481322550869637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67532921383900386937971397 12662422759481322550869637)
        ·
          refine ⟨2374204267402747978288057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12662422759481322550869637 2374204267402747978288057)
          ·
            refine ⟨1780653200552060983716043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2374204267402747978288057 1780653200552060983716043)
            ·
              refine ⟨2670979800828091475574065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1780653200552060983716043 2670979800828091475574065)
              ·
                refine ⟨2003234850621068606680549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2670979800828091475574065 2003234850621068606680549)
                ·
                  refine ⟨375606534491450363752603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2003234850621068606680549 375606534491450363752603)
                  ·
                    rfl

theorem cell21_1645855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 4].length) (baseStart_1645855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1645855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1645855 prefixEnd_1645855 := by exact prefixLift 1645855
  have htrace : WordTrace (prefixWord ++ tailWord_1645855) baseStart_1645855 baseEnd_1645855 := by
    simpa [prefixWord, tailWord_1645855, baseEnd_1645855] using wordTrace_append hprefix tailTrace_1645855
  have hstable : (prefixWord ++ tailWord_1645855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645855).length < 2 ^ (prefixWord ++ tailWord_1645855).sum := by decide
  have hdescent : baseEnd_1645855 < baseStart_1645855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645900 : List Nat := [2, 2, 1, 3, 2, 2, 3, 3, 3]
def baseStart_1645900 : Nat := 118140960795 + 1645900 * 2 ^ 59
def prefixEnd_1645900 : Nat := 4983230072969 + 3 ^ 40 * 1645900 * 2
def baseEnd_1645900 : Nat := 375616804104540285502511

theorem tailTrace_1645900 : CollatzResearch.WordTrace tailWord_1645900 prefixEnd_1645900 375616804104540285502511 := by
  unfold tailWord_1645900
  simp only [CollatzResearch.WordTrace]
  refine ⟨30015452368596436092903577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40020603158128581457204769 30015452368596436092903577)
  ·
    refine ⟨22511589276447327069677683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30015452368596436092903577 22511589276447327069677683)
    ·
      refine ⟨33767383914670990604516525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22511589276447327069677683 33767383914670990604516525)
      ·
        refine ⟨12662768968001621476693697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33767383914670990604516525 12662768968001621476693697)
        ·
          refine ⟨9497076726001216107520273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12662768968001621476693697 9497076726001216107520273)
          ·
            refine ⟨7122807544500912080640205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9497076726001216107520273 7122807544500912080640205)
            ·
              refine ⟨2671052829187842030240077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7122807544500912080640205 2671052829187842030240077)
              ·
                refine ⟨1001644810945440761340029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2671052829187842030240077 1001644810945440761340029)
                ·
                  refine ⟨375616804104540285502511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1001644810945440761340029 375616804104540285502511)
                  ·
                    rfl

theorem cell21_1645900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 3].length) (baseStart_1645900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1645900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1645900 prefixEnd_1645900 := by exact prefixLift 1645900
  have htrace : WordTrace (prefixWord ++ tailWord_1645900) baseStart_1645900 baseEnd_1645900 := by
    simpa [prefixWord, tailWord_1645900, baseEnd_1645900] using wordTrace_append hprefix tailTrace_1645900
  have hstable : (prefixWord ++ tailWord_1645900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645900).length < 2 ^ (prefixWord ++ tailWord_1645900).sum := by decide
  have hdescent : baseEnd_1645900 < baseStart_1645900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645911 : List Nat := [1, 1, 3, 2, 3, 2, 9]
def baseStart_1645911 : Nat := 118140960795 + 1645911 * 2 ^ 59
def prefixEnd_1645911 : Nat := 4983230072969 + 3 ^ 40 * 1645911 * 2
def baseEnd_1645911 : Nat := 41735479383822967868795

theorem tailTrace_1645911 : CollatzResearch.WordTrace tailWord_1645911 prefixEnd_1645911 41735479383822967868795 := by
  unfold tailWord_1645911
  simp only [CollatzResearch.WordTrace]
  refine ⟨60031305940153021064457587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40020870626768680709638391 60031305940153021064457587)
  ·
    refine ⟨90046958910229531596686381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60031305940153021064457587 90046958910229531596686381)
    ·
      refine ⟨33767609591336074348757393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90046958910229531596686381 33767609591336074348757393)
      ·
        refine ⟨25325707193502055761568045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33767609591336074348757393 25325707193502055761568045)
        ·
          refine ⟨9497140197563270910588017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25325707193502055761568045 9497140197563270910588017)
          ·
            refine ⟨7122855148172453182941013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9497140197563270910588017 7122855148172453182941013)
            ·
              refine ⟨41735479383822967868795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7122855148172453182941013 41735479383822967868795)
              ·
                rfl

theorem cell21_1645911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 9].length) (baseStart_1645911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1645911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1645911 prefixEnd_1645911 := by exact prefixLift 1645911
  have htrace : WordTrace (prefixWord ++ tailWord_1645911) baseStart_1645911 baseEnd_1645911 := by
    simpa [prefixWord, tailWord_1645911, baseEnd_1645911] using wordTrace_append hprefix tailTrace_1645911
  have hstable : (prefixWord ++ tailWord_1645911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645911).length < 2 ^ (prefixWord ++ tailWord_1645911).sum := by decide
  have hdescent : baseEnd_1645911 < baseStart_1645911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645973 : List Nat := [1, 3, 2, 1, 1, 2, 3, 4, 4]
def baseStart_1645973 : Nat := 118140960795 + 1645973 * 2 ^ 59
def prefixEnd_1645973 : Nat := 4983230072969 + 3 ^ 40 * 1645973 * 2
def baseEnd_1645973 : Nat := 375633463699108380785695

theorem tailTrace_1645973 : CollatzResearch.WordTrace tailWord_1645973 prefixEnd_1645973 375633463699108380785695 := by
  unfold tailWord_1645973
  simp only [CollatzResearch.WordTrace]
  refine ⟨60033567265928405653214573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40022378177285603768809715 60033567265928405653214573)
  ·
    refine ⟨22512587724723152119955465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60033567265928405653214573 22512587724723152119955465)
    ·
      refine ⟨16884440793542364089966599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22512587724723152119955465 16884440793542364089966599)
      ·
        refine ⟨25326661190313546134949899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16884440793542364089966599 25326661190313546134949899)
        ·
          refine ⟨37989991785470319202424849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25326661190313546134949899 37989991785470319202424849)
          ·
            refine ⟨28492493839102739401818637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37989991785470319202424849 28492493839102739401818637)
            ·
              refine ⟨10684685189663527275681989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28492493839102739401818637 10684685189663527275681989)
              ·
                refine ⟨2003378473061911364190373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10684685189663527275681989 2003378473061911364190373)
                ·
                  refine ⟨375633463699108380785695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2003378473061911364190373 375633463699108380785695)
                  ·
                    rfl

theorem cell21_1645973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_1645973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1645973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1645973 prefixEnd_1645973 := by exact prefixLift 1645973
  have htrace : WordTrace (prefixWord ++ tailWord_1645973) baseStart_1645973 baseEnd_1645973 := by
    simpa [prefixWord, tailWord_1645973, baseEnd_1645973] using wordTrace_append hprefix tailTrace_1645973
  have hstable : (prefixWord ++ tailWord_1645973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645973).length < 2 ^ (prefixWord ++ tailWord_1645973).sum := by decide
  have hdescent : baseEnd_1645973 < baseStart_1645973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646032 : List Nat := [2, 1, 1, 1, 1, 2, 2, 5, 6]
def baseStart_1646032 : Nat := 118140960795 + 1646032 * 2 ^ 59
def prefixEnd_1646032 : Nat := 4983230072969 + 3 ^ 40 * 1646032 * 2
def baseEnd_1646032 : Nat := 375646928302937389302241

theorem tailTrace_1646032 : CollatzResearch.WordTrace tailWord_1646032 prefixEnd_1646032 375646928302937389302241 := by
  unfold tailWord_1646032
  simp only [CollatzResearch.WordTrace]
  refine ⟨30017859586357329364806175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40023812781809772486408233 30017859586357329364806175)
  ·
    refine ⟨45026789379535994047209263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30017859586357329364806175 45026789379535994047209263)
    ·
      refine ⟨67540184069303991070813895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45026789379535994047209263 67540184069303991070813895)
      ·
        refine ⟨101310276103955986606220843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67540184069303991070813895 101310276103955986606220843)
        ·
          refine ⟨151965414155933979909331265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101310276103955986606220843 151965414155933979909331265)
          ·
            refine ⟨113974060616950484931998449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151965414155933979909331265 113974060616950484931998449)
            ·
              refine ⟨85480545462712863698998837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113974060616950484931998449 85480545462712863698998837)
              ·
                refine ⟨8013801137129330971781141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85480545462712863698998837 8013801137129330971781141)
                ·
                  refine ⟨375646928302937389302241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8013801137129330971781141 375646928302937389302241)
                  ·
                    rfl

theorem cell21_1646032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 6].length) (baseStart_1646032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1646032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1646032 prefixEnd_1646032 := by exact prefixLift 1646032
  have htrace : WordTrace (prefixWord ++ tailWord_1646032) baseStart_1646032 baseEnd_1646032 := by
    simpa [prefixWord, tailWord_1646032, baseEnd_1646032] using wordTrace_append hprefix tailTrace_1646032
  have hstable : (prefixWord ++ tailWord_1646032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646032).length < 2 ^ (prefixWord ++ tailWord_1646032).sum := by decide
  have hdescent : baseEnd_1646032 < baseStart_1646032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
