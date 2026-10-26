import V185TrunkScan21Chunk014

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_181553 : List Nat := [1, 2, 2, 3, 3, 2, 1, 7]
def baseStart_181553 : Nat := 118140960795 + 181553 * 2 ^ 59
def prefixEnd_181553 : Nat := 4983230072969 + 3 ^ 40 * 181553 * 2
def baseEnd_181553 : Nat := 13810956039382726926305

theorem tailTrace_181553 : CollatzResearch.WordTrace tailWord_181553 prefixEnd_181553 13810956039382726926305 := by
  unfold tailWord_181553
  simp only [CollatzResearch.WordTrace]
  refine ⟨6621781911271962628933313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4414521274181308419288875 6621781911271962628933313)
  ·
    refine ⟨4966336433453971971699985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6621781911271962628933313 4966336433453971971699985)
    ·
      refine ⟨3724752325090478978774989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4966336433453971971699985 3724752325090478978774989)
      ·
        refine ⟨1396782121908929617040621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3724752325090478978774989 1396782121908929617040621)
        ·
          refine ⟨523793295715848606390233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1396782121908929617040621 523793295715848606390233)
          ·
            refine ⟨392844971786886454792675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 523793295715848606390233 392844971786886454792675)
            ·
              refine ⟨589267457680329682189013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392844971786886454792675 589267457680329682189013)
              ·
                refine ⟨13810956039382726926305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 589267457680329682189013 13810956039382726926305)
                ·
                  rfl

theorem cell21_181553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 7].length) (baseStart_181553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_181553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_181553 prefixEnd_181553 := by exact prefixLift 181553
  have htrace : WordTrace (prefixWord ++ tailWord_181553) baseStart_181553 baseEnd_181553 := by
    simpa [prefixWord, tailWord_181553, baseEnd_181553] using wordTrace_append hprefix tailTrace_181553
  have hstable : (prefixWord ++ tailWord_181553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181553).length < 2 ^ (prefixWord ++ tailWord_181553).sum := by decide
  have hdescent : baseEnd_181553 < baseStart_181553 := by decide
  rcases family_descends (prefixWord ++ tailWord_181553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181643 : List Nat := [1, 1, 1, 1, 4, 3, 2, 3, 5]
def baseStart_181643 : Nat := 118140960795 + 181643 * 2 ^ 59
def prefixEnd_181643 : Nat := 4983230072969 + 3 ^ 40 * 181643 * 2
def baseEnd_181643 : Nat := 41453407344328024278731

theorem tailTrace_181643 : CollatzResearch.WordTrace tailWord_181643 prefixEnd_181643 41453407344328024278731 := by
  unfold tailWord_181643
  simp only [CollatzResearch.WordTrace]
  refine ⟨6625064480945907999709583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4416709653963938666473055 6625064480945907999709583)
  ·
    refine ⟨9937596721418861999564375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6625064480945907999709583 9937596721418861999564375)
    ·
      refine ⟨14906395082128292999346563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9937596721418861999564375 14906395082128292999346563)
      ·
        refine ⟨22359592623192439499019845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14906395082128292999346563 22359592623192439499019845)
        ·
          refine ⟨4192423616848582406066221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22359592623192439499019845 4192423616848582406066221)
          ·
            refine ⟨1572158856318218402274833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4192423616848582406066221 1572158856318218402274833)
            ·
              refine ⟨1179119142238663801706125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1572158856318218402274833 1179119142238663801706125)
              ·
                refine ⟨442169678339498925639797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1179119142238663801706125 442169678339498925639797)
                ·
                  refine ⟨41453407344328024278731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 442169678339498925639797 41453407344328024278731)
                  ·
                    rfl

theorem cell21_181643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 5].length) (baseStart_181643 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_181643 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_181643 prefixEnd_181643 := by exact prefixLift 181643
  have htrace : WordTrace (prefixWord ++ tailWord_181643) baseStart_181643 baseEnd_181643 := by
    simpa [prefixWord, tailWord_181643, baseEnd_181643] using wordTrace_append hprefix tailTrace_181643
  have hstable : (prefixWord ++ tailWord_181643).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181643).length < 2 ^ (prefixWord ++ tailWord_181643).sum := by decide
  have hdescent : baseEnd_181643 < baseStart_181643 := by decide
  rcases family_descends (prefixWord ++ tailWord_181643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181708 : List Nat := [2, 2, 1, 4, 2, 2, 3, 1, 4]
def baseStart_181708 : Nat := 118140960795 + 181708 * 2 ^ 59
def prefixEnd_181708 : Nat := 4983230072969 + 3 ^ 40 * 181708 * 2
def baseEnd_181708 : Nat := 41468241229902355695265

theorem tailTrace_181708 : CollatzResearch.WordTrace tailWord_181708 prefixEnd_181708 41468241229902355695265 := by
  unfold tailWord_181708
  simp only [CollatzResearch.WordTrace]
  refine ⟨3313717612855212050412889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4418290150473616067217185 3313717612855212050412889)
  ·
    refine ⟨2485288209641409037809667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3313717612855212050412889 2485288209641409037809667)
    ·
      refine ⟨3727932314462113556714501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2485288209641409037809667 3727932314462113556714501)
      ·
        refine ⟨698987308961646291883969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3727932314462113556714501 698987308961646291883969)
        ·
          refine ⟨524240481721234718912977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 698987308961646291883969 524240481721234718912977)
          ·
            refine ⟨393180361290926039184733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 524240481721234718912977 393180361290926039184733)
            ·
              refine ⟨147442635484097264694275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 393180361290926039184733 147442635484097264694275)
              ·
                refine ⟨221163953226145897041413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147442635484097264694275 221163953226145897041413)
                ·
                  refine ⟨41468241229902355695265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 221163953226145897041413 41468241229902355695265)
                  ·
                    rfl

theorem cell21_181708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_181708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_181708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_181708 prefixEnd_181708 := by exact prefixLift 181708
  have htrace : WordTrace (prefixWord ++ tailWord_181708) baseStart_181708 baseEnd_181708 := by
    simpa [prefixWord, tailWord_181708, baseEnd_181708] using wordTrace_append hprefix tailTrace_181708
  have hstable : (prefixWord ++ tailWord_181708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181708).length < 2 ^ (prefixWord ++ tailWord_181708).sum := by decide
  have hdescent : baseEnd_181708 < baseStart_181708 := by decide
  rcases family_descends (prefixWord ++ tailWord_181708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181722 : List Nat := [3, 1, 1, 2, 3, 4, 2, 5]
def baseStart_181722 : Nat := 118140960795 + 181722 * 2 ^ 59
def prefixEnd_181722 : Nat := 4983230072969 + 3 ^ 40 * 181722 * 2
def baseEnd_181722 : Nat := 13823812073547147487301

theorem tailTrace_181722 : CollatzResearch.WordTrace tailWord_181722 prefixEnd_181722 13823812073547147487301 := by
  unfold tailWord_181722
  simp only [CollatzResearch.WordTrace]
  refine ⟨1656986461914926122958855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4418630565106469661223613 1656986461914926122958855)
  ·
    refine ⟨2485479692872389184438283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1656986461914926122958855 2485479692872389184438283)
    ·
      refine ⟨3728219539308583776657425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2485479692872389184438283 3728219539308583776657425)
      ·
        refine ⟨2796164654481437832493069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3728219539308583776657425 2796164654481437832493069)
        ·
          refine ⟨1048561745430539187184901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2796164654481437832493069 1048561745430539187184901)
          ·
            refine ⟨196605327268226097597169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1048561745430539187184901 196605327268226097597169)
            ·
              refine ⟨147453995451169573197877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196605327268226097597169 147453995451169573197877)
              ·
                refine ⟨13823812073547147487301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 147453995451169573197877 13823812073547147487301)
                ·
                  rfl

theorem cell21_181722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 5].length) (baseStart_181722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_181722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_181722 prefixEnd_181722 := by exact prefixLift 181722
  have htrace : WordTrace (prefixWord ++ tailWord_181722) baseStart_181722 baseEnd_181722 := by
    simpa [prefixWord, tailWord_181722, baseEnd_181722] using wordTrace_append hprefix tailTrace_181722
  have hstable : (prefixWord ++ tailWord_181722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181722).length < 2 ^ (prefixWord ++ tailWord_181722).sum := by decide
  have hdescent : baseEnd_181722 < baseStart_181722 := by decide
  rcases family_descends (prefixWord ++ tailWord_181722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181767 : List Nat := [1, 1, 4, 3, 2, 2, 1, 3, 4]
def baseStart_181767 : Nat := 118140960795 + 181767 * 2 ^ 59
def prefixEnd_181767 : Nat := 4983230072969 + 3 ^ 40 * 181767 * 2
def baseEnd_181767 : Nat := 41481705833731364211811

theorem tailTrace_181767 : CollatzResearch.WordTrace tailWord_181767 prefixEnd_181767 41481705833731364211811 := by
  unfold tailWord_181767
  simp only [CollatzResearch.WordTrace]
  refine ⟨6629587132496677177223555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4419724754997784784815703 6629587132496677177223555)
  ·
    refine ⟨9944380698745015765835333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6629587132496677177223555 9944380698745015765835333)
    ·
      refine ⟨1864571381014690456094125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9944380698745015765835333 1864571381014690456094125)
      ·
        refine ⟨699214267880508921035297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1864571381014690456094125 699214267880508921035297)
        ·
          refine ⟨524410700910381690776473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 699214267880508921035297 524410700910381690776473)
          ·
            refine ⟨393308025682786268082355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 524410700910381690776473 393308025682786268082355)
            ·
              refine ⟨589962038524179402123533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393308025682786268082355 589962038524179402123533)
              ·
                refine ⟨221235764446567275796325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 589962038524179402123533 221235764446567275796325)
                ·
                  refine ⟨41481705833731364211811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 221235764446567275796325 41481705833731364211811)
                  ·
                    rfl

theorem cell21_181767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 4].length) (baseStart_181767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_181767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_181767 prefixEnd_181767 := by exact prefixLift 181767
  have htrace : WordTrace (prefixWord ++ tailWord_181767) baseStart_181767 baseEnd_181767 := by
    simpa [prefixWord, tailWord_181767, baseEnd_181767] using wordTrace_append hprefix tailTrace_181767
  have hstable : (prefixWord ++ tailWord_181767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181767).length < 2 ^ (prefixWord ++ tailWord_181767).sum := by decide
  have hdescent : baseEnd_181767 < baseStart_181767 := by decide
  rcases family_descends (prefixWord ++ tailWord_181767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181902 : List Nat := [4, 1, 1, 3, 1, 2, 1, 2, 6]
def baseStart_181902 : Nat := 118140960795 + 181902 * 2 ^ 59
def prefixEnd_181902 : Nat := 4983230072969 + 3 ^ 40 * 181902 * 2
def baseEnd_181902 : Nat := 41512514673001129461535

theorem tailTrace_181902 : CollatzResearch.WordTrace tailWord_181902 prefixEnd_181902 41512514673001129461535 := by
  unfold tailWord_181902
  simp only [CollatzResearch.WordTrace]
  refine ⟨829313873375949404173495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4423007324671730155591973 829313873375949404173495)
  ·
    refine ⟨1243970810063924106260243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 829313873375949404173495 1243970810063924106260243)
    ·
      refine ⟨1865956215095886159390365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1243970810063924106260243 1865956215095886159390365)
      ·
        refine ⟨699733580660957309771387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1865956215095886159390365 699733580660957309771387)
        ·
          refine ⟨1049600370991435964657081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 699733580660957309771387 1049600370991435964657081)
          ·
            refine ⟨787200278243576973492811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1049600370991435964657081 787200278243576973492811)
            ·
              refine ⟨1180800417365365460239217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787200278243576973492811 1180800417365365460239217)
              ·
                refine ⟨885600313024024095179413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1180800417365365460239217 885600313024024095179413)
                ·
                  refine ⟨41512514673001129461535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 885600313024024095179413 41512514673001129461535)
                  ·
                    rfl

theorem cell21_181902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_181902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_181902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_181902 prefixEnd_181902 := by exact prefixLift 181902
  have htrace : WordTrace (prefixWord ++ tailWord_181902) baseStart_181902 baseEnd_181902 := by
    simpa [prefixWord, tailWord_181902, baseEnd_181902] using wordTrace_append hprefix tailTrace_181902
  have hstable : (prefixWord ++ tailWord_181902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181902).length < 2 ^ (prefixWord ++ tailWord_181902).sum := by decide
  have hdescent : baseEnd_181902 < baseStart_181902 := by decide
  rcases family_descends (prefixWord ++ tailWord_181902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181922 : List Nat := [3, 3, 1, 4, 1, 2, 1, 1, 5]
def baseStart_181922 : Nat := 118140960795 + 181922 * 2 ^ 59
def prefixEnd_181922 : Nat := 4983230072969 + 3 ^ 40 * 181922 * 2
def baseEnd_181922 : Nat := 41517078945485539128161

theorem tailTrace_181922 : CollatzResearch.WordTrace tailWord_181922 prefixEnd_181922 41517078945485539128161 := by
  unfold tailWord_181922
  simp only [CollatzResearch.WordTrace]
  refine ⟨1658810111733784662279005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4423493631290092432744013 1658810111733784662279005)
  ·
    refine ⟨622053791900169248354627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1658810111733784662279005 622053791900169248354627)
    ·
      refine ⟨933080687850253872531941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 622053791900169248354627 933080687850253872531941)
      ·
        refine ⟨174952628971922601099739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 933080687850253872531941 174952628971922601099739)
        ·
          refine ⟨262428943457883901649609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174952628971922601099739 262428943457883901649609)
          ·
            refine ⟨196821707593412926237207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262428943457883901649609 196821707593412926237207)
            ·
              refine ⟨295232561390119389355811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196821707593412926237207 295232561390119389355811)
              ·
                refine ⟨442848842085179084033717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295232561390119389355811 442848842085179084033717)
                ·
                  refine ⟨41517078945485539128161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 442848842085179084033717 41517078945485539128161)
                  ·
                    rfl

theorem cell21_181922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_181922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_181922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_181922 prefixEnd_181922 := by exact prefixLift 181922
  have htrace : WordTrace (prefixWord ++ tailWord_181922) baseStart_181922 baseEnd_181922 := by
    simpa [prefixWord, tailWord_181922, baseEnd_181922] using wordTrace_append hprefix tailTrace_181922
  have hstable : (prefixWord ++ tailWord_181922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181922).length < 2 ^ (prefixWord ++ tailWord_181922).sum := by decide
  have hdescent : baseEnd_181922 < baseStart_181922 := by decide
  rcases family_descends (prefixWord ++ tailWord_181922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181933 : List Nat := [1, 5, 2, 1, 1, 1, 4, 6]
def baseStart_181933 : Nat := 118140960795 + 181933 * 2 ^ 59
def prefixEnd_181933 : Nat := 4983230072969 + 3 ^ 40 * 181933 * 2
def baseEnd_181933 : Nat := 13839863098450654814935

theorem tailTrace_181933 : CollatzResearch.WordTrace tailWord_181933 prefixEnd_181933 13839863098450654814935 := by
  unfold tailWord_181933
  simp only [CollatzResearch.WordTrace]
  refine ⟨6635641649895287527766453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4423761099930191685177635 6635641649895287527766453)
  ·
    refine ⟨622091404677683205728105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6635641649895287527766453 622091404677683205728105)
    ·
      refine ⟨466568553508262404296079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 622091404677683205728105 466568553508262404296079)
      ·
        refine ⟨699852830262393606444119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466568553508262404296079 699852830262393606444119)
        ·
          refine ⟨1049779245393590409666179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 699852830262393606444119 1049779245393590409666179)
          ·
            refine ⟨1574668868090385614499269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1049779245393590409666179 1574668868090385614499269)
            ·
              refine ⟨295250412766947302718613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1574668868090385614499269 295250412766947302718613)
              ·
                refine ⟨13839863098450654814935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 295250412766947302718613 13839863098450654814935)
                ·
                  rfl

theorem cell21_181933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 6].length) (baseStart_181933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_181933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_181933 prefixEnd_181933 := by exact prefixLift 181933
  have htrace : WordTrace (prefixWord ++ tailWord_181933) baseStart_181933 baseEnd_181933 := by
    simpa [prefixWord, tailWord_181933, baseEnd_181933] using wordTrace_append hprefix tailTrace_181933
  have hstable : (prefixWord ++ tailWord_181933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181933).length < 2 ^ (prefixWord ++ tailWord_181933).sum := by decide
  have hdescent : baseEnd_181933 < baseStart_181933 := by decide
  rcases family_descends (prefixWord ++ tailWord_181933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181978 : List Nat := [3, 1, 1, 2, 2, 3, 1, 4, 4]
def baseStart_181978 : Nat := 118140960795 + 181978 * 2 ^ 59
def prefixEnd_181978 : Nat := 4983230072969 + 3 ^ 40 * 181978 * 2
def baseEnd_181978 : Nat := 41529858908441886194713

theorem tailTrace_181978 : CollatzResearch.WordTrace tailWord_181978 prefixEnd_181978 41529858908441886194713 := by
  unfold tailWord_181978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1659320733683065053288647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4424855289821506808769725 1659320733683065053288647)
  ·
    refine ⟨2488981100524597579932971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1659320733683065053288647 2488981100524597579932971)
    ·
      refine ⟨3733471650786896369899457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2488981100524597579932971 3733471650786896369899457)
      ·
        refine ⟨2800103738090172277424593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3733471650786896369899457 2800103738090172277424593)
        ·
          refine ⟨2100077803567629208068445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2800103738090172277424593 2100077803567629208068445)
          ·
            refine ⟨787529176337860953025667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2100077803567629208068445 787529176337860953025667)
            ·
              refine ⟨1181293764506791429538501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787529176337860953025667 1181293764506791429538501)
              ·
                refine ⟨221492580845023393038469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1181293764506791429538501 221492580845023393038469)
                ·
                  refine ⟨41529858908441886194713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 221492580845023393038469 41529858908441886194713)
                  ·
                    rfl

theorem cell21_181978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_181978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_181978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_181978 prefixEnd_181978 := by exact prefixLift 181978
  have htrace : WordTrace (prefixWord ++ tailWord_181978) baseStart_181978 baseEnd_181978 := by
    simpa [prefixWord, tailWord_181978, baseEnd_181978] using wordTrace_append hprefix tailTrace_181978
  have hstable : (prefixWord ++ tailWord_181978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181978).length < 2 ^ (prefixWord ++ tailWord_181978).sum := by decide
  have hdescent : baseEnd_181978 < baseStart_181978 := by decide
  rcases family_descends (prefixWord ++ tailWord_181978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182040 : List Nat := [2, 1, 2, 3, 1, 1, 4, 4, 3]
def baseStart_182040 : Nat := 118140960795 + 182040 * 2 ^ 59
def prefixEnd_182040 : Nat := 4983230072969 + 3 ^ 40 * 182040 * 2
def baseEnd_182040 : Nat := 41544008153143556161253

theorem tailTrace_182040 : CollatzResearch.WordTrace tailWord_182040 prefixEnd_182040 41544008153143556161253 := by
  unfold tailWord_182040
  simp only [CollatzResearch.WordTrace]
  refine ⟨3319772130253822400955787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4426362840338429867941049 3319772130253822400955787)
  ·
    refine ⟨4979658195380733601433681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3319772130253822400955787 4979658195380733601433681)
    ·
      refine ⟨3734743646535550201075261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4979658195380733601433681 3734743646535550201075261)
      ·
        refine ⟨1400528867450831325403223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3734743646535550201075261 1400528867450831325403223)
        ·
          refine ⟨2100793301176246988104835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1400528867450831325403223 2100793301176246988104835)
          ·
            refine ⟨3151189951764370482157253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2100793301176246988104835 3151189951764370482157253)
            ·
              refine ⟨590848115955819465404485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3151189951764370482157253 590848115955819465404485)
              ·
                refine ⟨110784021741716149763341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 590848115955819465404485 110784021741716149763341)
                ·
                  refine ⟨41544008153143556161253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110784021741716149763341 41544008153143556161253)
                  ·
                    rfl

theorem cell21_182040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4, 3].length) (baseStart_182040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_182040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_182040 prefixEnd_182040 := by exact prefixLift 182040
  have htrace : WordTrace (prefixWord ++ tailWord_182040) baseStart_182040 baseEnd_182040 := by
    simpa [prefixWord, tailWord_182040, baseEnd_182040] using wordTrace_append hprefix tailTrace_182040
  have hstable : (prefixWord ++ tailWord_182040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182040).length < 2 ^ (prefixWord ++ tailWord_182040).sum := by decide
  have hdescent : baseEnd_182040 < baseStart_182040 := by decide
  rcases family_descends (prefixWord ++ tailWord_182040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182046 : List Nat := [4, 3, 2, 2, 1, 1, 3, 1, 4]
def baseStart_182046 : Nat := 118140960795 + 182046 * 2 ^ 59
def prefixEnd_182046 : Nat := 4983230072969 + 3 ^ 40 * 182046 * 2
def baseEnd_182046 : Nat := 41545377434888879061241

theorem tailTrace_182046 : CollatzResearch.WordTrace tailWord_182046 prefixEnd_182046 41545377434888879061241 := by
  unfold tailWord_182046
  simp only [CollatzResearch.WordTrace]
  refine ⟨829970387310738478328749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4426508732323938551086661 829970387310738478328749)
  ·
    refine ⟨311238895241526929373281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 829970387310738478328749 311238895241526929373281)
    ·
      refine ⟨233429171431145197029961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311238895241526929373281 233429171431145197029961)
      ·
        refine ⟨175071878573358897772471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233429171431145197029961 175071878573358897772471)
        ·
          refine ⟨262607817860038346658707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175071878573358897772471 262607817860038346658707)
          ·
            refine ⟨393911726790057519988061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262607817860038346658707 393911726790057519988061)
            ·
              refine ⟨147716897546271569995523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 393911726790057519988061 147716897546271569995523)
              ·
                refine ⟨221575346319407354993285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147716897546271569995523 221575346319407354993285)
                ·
                  refine ⟨41545377434888879061241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 221575346319407354993285 41545377434888879061241)
                  ·
                    rfl

theorem cell21_182046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_182046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_182046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_182046 prefixEnd_182046 := by exact prefixLift 182046
  have htrace : WordTrace (prefixWord ++ tailWord_182046) baseStart_182046 baseEnd_182046 := by
    simpa [prefixWord, tailWord_182046, baseEnd_182046] using wordTrace_append hprefix tailTrace_182046
  have hstable : (prefixWord ++ tailWord_182046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182046).length < 2 ^ (prefixWord ++ tailWord_182046).sum := by decide
  have hdescent : baseEnd_182046 < baseStart_182046 := by decide
  rcases family_descends (prefixWord ++ tailWord_182046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182178 : List Nat := [3, 3, 1, 2, 3, 1, 3, 5]
def baseStart_182178 : Nat := 118140960795 + 182178 * 2 ^ 59
def prefixEnd_182178 : Nat := 4983230072969 + 3 ^ 40 * 182178 * 2
def baseEnd_182178 : Nat := 13858500544428660953657

theorem tailTrace_182178 : CollatzResearch.WordTrace tailWord_182178 prefixEnd_182178 13858500544428660953657 := by
  unfold tailWord_182178
  simp only [CollatzResearch.WordTrace]
  refine ⟨1661144383501923592608797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4429718356005129580290125 1661144383501923592608797)
  ·
    refine ⟨622929143813221347228299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1661144383501923592608797 622929143813221347228299)
    ·
      refine ⟨934393715719832020842449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 622929143813221347228299 934393715719832020842449)
      ·
        refine ⟨700795286789874015631837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 934393715719832020842449 700795286789874015631837)
        ·
          refine ⟨262798232546202755861939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 700795286789874015631837 262798232546202755861939)
          ·
            refine ⟨394197348819304133792909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262798232546202755861939 394197348819304133792909)
            ·
              refine ⟨147824005807239050172341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 394197348819304133792909 147824005807239050172341)
              ·
                refine ⟨13858500544428660953657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 147824005807239050172341 13858500544428660953657)
                ·
                  rfl

theorem cell21_182178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 5].length) (baseStart_182178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_182178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_182178 prefixEnd_182178 := by exact prefixLift 182178
  have htrace : WordTrace (prefixWord ++ tailWord_182178) baseStart_182178 baseEnd_182178 := by
    simpa [prefixWord, tailWord_182178, baseEnd_182178] using wordTrace_append hprefix tailTrace_182178
  have hstable : (prefixWord ++ tailWord_182178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182178).length < 2 ^ (prefixWord ++ tailWord_182178).sum := by decide
  have hdescent : baseEnd_182178 < baseStart_182178 := by decide
  rcases family_descends (prefixWord ++ tailWord_182178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182206 : List Nat := [4, 2, 1, 1, 1, 4, 1, 1, 6]
def baseStart_182206 : Nat := 118140960795 + 182206 * 2 ^ 59
def prefixEnd_182206 : Nat := 4983230072969 + 3 ^ 40 * 182206 * 2
def baseEnd_182206 : Nat := 41581891614764156394247

theorem tailTrace_182206 : CollatzResearch.WordTrace tailWord_182206 prefixEnd_182206 41581891614764156394247 := by
  unfold tailWord_182206
  simp only [CollatzResearch.WordTrace]
  refine ⟨830699847238281894056809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4430399185270836768302981 830699847238281894056809)
  ·
    refine ⟨623024885428711420542607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 830699847238281894056809 623024885428711420542607)
    ·
      refine ⟨934537328143067130813911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 623024885428711420542607 934537328143067130813911)
      ·
        refine ⟨1401805992214600696220867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 934537328143067130813911 1401805992214600696220867)
        ·
          refine ⟨2102708988321901044331301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1401805992214600696220867 2102708988321901044331301)
          ·
            refine ⟨394257935310356445812119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2102708988321901044331301 394257935310356445812119)
            ·
              refine ⟨591386902965534668718179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394257935310356445812119 591386902965534668718179)
              ·
                refine ⟨887080354448302003077269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 591386902965534668718179 887080354448302003077269)
                ·
                  refine ⟨41581891614764156394247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 887080354448302003077269 41581891614764156394247)
                  ·
                    rfl

theorem cell21_182206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_182206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_182206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_182206 prefixEnd_182206 := by exact prefixLift 182206
  have htrace : WordTrace (prefixWord ++ tailWord_182206) baseStart_182206 baseEnd_182206 := by
    simpa [prefixWord, tailWord_182206, baseEnd_182206] using wordTrace_append hprefix tailTrace_182206
  have hstable : (prefixWord ++ tailWord_182206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182206).length < 2 ^ (prefixWord ++ tailWord_182206).sum := by decide
  have hdescent : baseEnd_182206 < baseStart_182206 := by decide
  rcases family_descends (prefixWord ++ tailWord_182206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182237 : List Nat := [1, 4, 3, 1, 3, 1, 1, 7]
def baseStart_182237 : Nat := 118140960795 + 182237 * 2 ^ 59
def prefixEnd_182237 : Nat := 4983230072969 + 3 ^ 40 * 182237 * 2
def baseEnd_182237 : Nat := 13862988745704997125839

theorem tailTrace_182237 : CollatzResearch.WordTrace tailWord_182237 prefixEnd_182237 13862988745704997125839 := by
  unfold tailWord_182237
  simp only [CollatzResearch.WordTrace]
  refine ⟨6646729440793947446832965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4431152960529298297888643 6646729440793947446832965)
  ·
    refine ⟨1246261770148865146281181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6646729440793947446832965 1246261770148865146281181)
    ·
      refine ⟨467348163805824429855443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1246261770148865146281181 467348163805824429855443)
      ·
        refine ⟨701022245708736644783165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467348163805824429855443 701022245708736644783165)
        ·
          refine ⟨262883342140776241793687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 701022245708736644783165 262883342140776241793687)
          ·
            refine ⟨394325013211164362690531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262883342140776241793687 394325013211164362690531)
            ·
              refine ⟨591487519816746544035797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394325013211164362690531 591487519816746544035797)
              ·
                refine ⟨13862988745704997125839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 591487519816746544035797 13862988745704997125839)
                ·
                  rfl

theorem cell21_182237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 7].length) (baseStart_182237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_182237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_182237 prefixEnd_182237 := by exact prefixLift 182237
  have htrace : WordTrace (prefixWord ++ tailWord_182237) baseStart_182237 baseEnd_182237 := by
    simpa [prefixWord, tailWord_182237, baseEnd_182237] using wordTrace_append hprefix tailTrace_182237
  have hstable : (prefixWord ++ tailWord_182237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182237).length < 2 ^ (prefixWord ++ tailWord_182237).sum := by decide
  have hdescent : baseEnd_182237 < baseStart_182237 := by decide
  rcases family_descends (prefixWord ++ tailWord_182237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182265 : List Nat := [1, 2, 1, 3, 1, 4, 2, 1, 6]
def baseStart_182265 : Nat := 118140960795 + 182265 * 2 ^ 59
def prefixEnd_182265 : Nat := 4983230072969 + 3 ^ 40 * 182265 * 2
def baseEnd_182265 : Nat := 41595356218593164910793

theorem tailTrace_182265 : CollatzResearch.WordTrace tailWord_182265 prefixEnd_182265 41595356218593164910793 := by
  unfold tailWord_182265
  simp only [CollatzResearch.WordTrace]
  refine ⟨6647750684692508228852249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4431833789795005485901499 6647750684692508228852249)
  ·
    refine ⟨4985813013519381171639187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6647750684692508228852249 4985813013519381171639187)
    ·
      refine ⟨7478719520279071757458781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4985813013519381171639187 7478719520279071757458781)
      ·
        refine ⟨2804519820104651909047043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7478719520279071757458781 2804519820104651909047043)
        ·
          refine ⟨4206779730156977863570565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2804519820104651909047043 4206779730156977863570565)
          ·
            refine ⟨788771199404433349419481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4206779730156977863570565 788771199404433349419481)
            ·
              refine ⟨591578399553325012064611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 788771199404433349419481 591578399553325012064611)
              ·
                refine ⟨887367599329987518096917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 591578399553325012064611 887367599329987518096917)
                ·
                  refine ⟨41595356218593164910793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 887367599329987518096917 41595356218593164910793)
                  ·
                    rfl

theorem cell21_182265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 6].length) (baseStart_182265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_182265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_182265 prefixEnd_182265 := by exact prefixLift 182265
  have htrace : WordTrace (prefixWord ++ tailWord_182265) baseStart_182265 baseEnd_182265 := by
    simpa [prefixWord, tailWord_182265, baseEnd_182265] using wordTrace_append hprefix tailTrace_182265
  have hstable : (prefixWord ++ tailWord_182265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182265).length < 2 ^ (prefixWord ++ tailWord_182265).sum := by decide
  have hdescent : baseEnd_182265 < baseStart_182265 := by decide
  rcases family_descends (prefixWord ++ tailWord_182265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182434 : List Nat := [3, 3, 1, 3, 1, 1, 2, 1, 6]
def baseStart_182434 : Nat := 118140960795 + 182434 * 2 ^ 59
def prefixEnd_182434 : Nat := 4983230072969 + 3 ^ 40 * 182434 * 2
def baseEnd_182434 : Nat := 41633924321086426593781

theorem tailTrace_182434 : CollatzResearch.WordTrace tailWord_182434 prefixEnd_182434 41633924321086426593781 := by
  unfold tailWord_182434
  simp only [CollatzResearch.WordTrace]
  refine ⟨1663478655270062522938589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4435943080720166727836237 1663478655270062522938589)
  ·
    refine ⟨623804495726273446101971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1663478655270062522938589 623804495726273446101971)
    ·
      refine ⟨935706743589410169152957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 623804495726273446101971 935706743589410169152957)
      ·
        refine ⟨350890028846028813432359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 935706743589410169152957 350890028846028813432359)
        ·
          refine ⟨526335043269043220148539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350890028846028813432359 526335043269043220148539)
          ·
            refine ⟨789502564903564830222809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526335043269043220148539 789502564903564830222809)
            ·
              refine ⟨592126923677673622667107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 789502564903564830222809 592126923677673622667107)
              ·
                refine ⟨888190385516510434000661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592126923677673622667107 888190385516510434000661)
                ·
                  refine ⟨41633924321086426593781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 888190385516510434000661 41633924321086426593781)
                  ·
                    rfl

theorem cell21_182434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_182434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_182434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_182434 prefixEnd_182434 := by exact prefixLift 182434
  have htrace : WordTrace (prefixWord ++ tailWord_182434) baseStart_182434 baseEnd_182434 := by
    simpa [prefixWord, tailWord_182434, baseEnd_182434] using wordTrace_append hprefix tailTrace_182434
  have hstable : (prefixWord ++ tailWord_182434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182434).length < 2 ^ (prefixWord ++ tailWord_182434).sum := by decide
  have hdescent : baseEnd_182434 < baseStart_182434 := by decide
  rcases family_descends (prefixWord ++ tailWord_182434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182479 : List Nat := [1, 1, 2, 1, 1, 3, 4, 5, 3]
def baseStart_182479 : Nat := 118140960795 + 182479 * 2 ^ 59
def prefixEnd_182479 : Nat := 4983230072969 + 3 ^ 40 * 182479 * 2
def baseEnd_182479 : Nat := 41644193934176348343689

theorem tailTrace_182479 : CollatzResearch.WordTrace tailWord_182479 prefixEnd_182479 41644193934176348343689 := by
  unfold tailWord_182479
  simp only [CollatzResearch.WordTrace]
  refine ⟨6655555905917222777142491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4437037270611481851428327 6655555905917222777142491)
  ·
    refine ⟨9983333858875834165713737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6655555905917222777142491 9983333858875834165713737)
    ·
      refine ⟨7487500394156875624285303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9983333858875834165713737 7487500394156875624285303)
      ·
        refine ⟨11231250591235313436427955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7487500394156875624285303 11231250591235313436427955)
        ·
          refine ⟨16846875886852970154641933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11231250591235313436427955 16846875886852970154641933)
          ·
            refine ⟨6317578457569863807990725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16846875886852970154641933 6317578457569863807990725)
            ·
              refine ⟨1184545960794349463998261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6317578457569863807990725 1184545960794349463998261)
              ·
                refine ⟨111051183824470262249837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1184545960794349463998261 111051183824470262249837)
                ·
                  refine ⟨41644193934176348343689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111051183824470262249837 41644193934176348343689)
                  ·
                    rfl

theorem cell21_182479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 3].length) (baseStart_182479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_182479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_182479 prefixEnd_182479 := by exact prefixLift 182479
  have htrace : WordTrace (prefixWord ++ tailWord_182479) baseStart_182479 baseEnd_182479 := by
    simpa [prefixWord, tailWord_182479, baseEnd_182479] using wordTrace_append hprefix tailTrace_182479
  have hstable : (prefixWord ++ tailWord_182479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182479).length < 2 ^ (prefixWord ++ tailWord_182479).sum := by decide
  have hdescent : baseEnd_182479 < baseStart_182479 := by decide
  rcases family_descends (prefixWord ++ tailWord_182479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182555 : List Nat := [1, 1, 1, 1, 1, 1, 8, 4, 3]
def baseStart_182555 : Nat := 118140960795 + 182555 * 2 ^ 59
def prefixEnd_182555 : Nat := 4983230072969 + 3 ^ 40 * 182555 * 2
def baseEnd_182555 : Nat := 41661538169617105076867

theorem tailTrace_182555 : CollatzResearch.WordTrace tailWord_182555 prefixEnd_182555 41661538169617105076867 := by
  unfold tailWord_182555
  simp only [CollatzResearch.WordTrace]
  refine ⟨6658327853641887756909119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4438885235761258504606079 6658327853641887756909119)
  ·
    refine ⟨9987491780462831635363679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6658327853641887756909119 9987491780462831635363679)
    ·
      refine ⟨14981237670694247453045519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9987491780462831635363679 14981237670694247453045519)
      ·
        refine ⟨22471856506041371179568279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14981237670694247453045519 22471856506041371179568279)
        ·
          refine ⟨33707784759062056769352419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22471856506041371179568279 33707784759062056769352419)
          ·
            refine ⟨50561677138593085154028629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33707784759062056769352419 50561677138593085154028629)
            ·
              refine ⟨592519653967887716648773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 50561677138593085154028629 592519653967887716648773)
              ·
                refine ⟨111097435118978946871645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 592519653967887716648773 111097435118978946871645)
                ·
                  refine ⟨41661538169617105076867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111097435118978946871645 41661538169617105076867)
                  ·
                    rfl

theorem cell21_182555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4, 3].length) (baseStart_182555 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_182555 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_182555 prefixEnd_182555 := by exact prefixLift 182555
  have htrace : WordTrace (prefixWord ++ tailWord_182555) baseStart_182555 baseEnd_182555 := by
    simpa [prefixWord, tailWord_182555, baseEnd_182555] using wordTrace_append hprefix tailTrace_182555
  have hstable : (prefixWord ++ tailWord_182555).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182555).length < 2 ^ (prefixWord ++ tailWord_182555).sum := by decide
  have hdescent : baseEnd_182555 < baseStart_182555 := by decide
  rcases family_descends (prefixWord ++ tailWord_182555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182659 : List Nat := [1, 1, 1, 3, 6, 9]
def baseStart_182659 : Nat := 118140960795 + 182659 * 2 ^ 59
def prefixEnd_182659 : Nat := 4983230072969 + 3 ^ 40 * 182659 * 2
def baseEnd_182659 : Nat := 1543898977279112420123

theorem tailTrace_182659 : CollatzResearch.WordTrace tailWord_182659 prefixEnd_182659 1543898977279112420123 := by
  unfold tailWord_182659
  simp only [CollatzResearch.WordTrace]
  refine ⟨6662121045265113518695031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4441414030176742345796687 6662121045265113518695031)
  ·
    refine ⟨9993181567897670278042547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6662121045265113518695031 9993181567897670278042547)
    ·
      refine ⟨14989772351846505417063821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9993181567897670278042547 14989772351846505417063821)
      ·
        refine ⟨5621164631942439531398933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14989772351846505417063821 5621164631942439531398933)
        ·
          refine ⟨263492092122301853034325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5621164631942439531398933 263492092122301853034325)
          ·
            refine ⟨1543898977279112420123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 263492092122301853034325 1543898977279112420123)
            ·
              rfl

theorem cell21_182659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 9].length) (baseStart_182659 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_182659 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_182659 prefixEnd_182659 := by exact prefixLift 182659
  have htrace : WordTrace (prefixWord ++ tailWord_182659) baseStart_182659 baseEnd_182659 := by
    simpa [prefixWord, tailWord_182659, baseEnd_182659] using wordTrace_append hprefix tailTrace_182659
  have hstable : (prefixWord ++ tailWord_182659).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182659).length < 2 ^ (prefixWord ++ tailWord_182659).sum := by decide
  have hdescent : baseEnd_182659 < baseStart_182659 := by decide
  rcases family_descends (prefixWord ++ tailWord_182659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182665 : List Nat := [1, 2, 1, 1, 6, 3, 2, 2, 3]
def baseStart_182665 : Nat := 118140960795 + 182665 * 2 ^ 59
def prefixEnd_182665 : Nat := 4983230072969 + 3 ^ 40 * 182665 * 2
def baseEnd_182665 : Nat := 41686641668281358243309

theorem tailTrace_182665 : CollatzResearch.WordTrace tailWord_182665 prefixEnd_182665 41686641668281358243309 := by
  unfold tailWord_182665
  simp only [CollatzResearch.WordTrace]
  refine ⟨6662339883243376543413449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4441559922162251028942299 6662339883243376543413449)
  ·
    refine ⟨4996754912432532407560087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6662339883243376543413449 4996754912432532407560087)
    ·
      refine ⟨7495132368648798611340131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4996754912432532407560087 7495132368648798611340131)
      ·
        refine ⟨11242698552973197917010197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7495132368648798611340131 11242698552973197917010197)
        ·
          refine ⟨527001494670618652359853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11242698552973197917010197 527001494670618652359853)
          ·
            refine ⟨197625560501481994634945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 527001494670618652359853 197625560501481994634945)
            ·
              refine ⟨148219170376111495976209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197625560501481994634945 148219170376111495976209)
              ·
                refine ⟨111164377782083621982157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148219170376111495976209 111164377782083621982157)
                ·
                  refine ⟨41686641668281358243309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111164377782083621982157 41686641668281358243309)
                  ·
                    rfl

theorem cell21_182665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2, 3].length) (baseStart_182665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_182665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_182665 prefixEnd_182665 := by exact prefixLift 182665
  have htrace : WordTrace (prefixWord ++ tailWord_182665) baseStart_182665 baseEnd_182665 := by
    simpa [prefixWord, tailWord_182665, baseEnd_182665] using wordTrace_append hprefix tailTrace_182665
  have hstable : (prefixWord ++ tailWord_182665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182665).length < 2 ^ (prefixWord ++ tailWord_182665).sum := by decide
  have hdescent : baseEnd_182665 < baseStart_182665 := by decide
  rcases family_descends (prefixWord ++ tailWord_182665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182724 : List Nat := [2, 3, 3, 2, 2, 1, 2, 1, 5]
def baseStart_182724 : Nat := 118140960795 + 182724 * 2 ^ 59
def prefixEnd_182724 : Nat := 4983230072969 + 3 ^ 40 * 182724 * 2
def baseEnd_182724 : Nat := 41700106272110366759855

theorem tailTrace_182724 : CollatzResearch.WordTrace tailWord_182724 prefixEnd_182724 41700106272110366759855 := by
  unfold tailWord_182724
  simp only [CollatzResearch.WordTrace]
  refine ⟨3332245895014814809905613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4442994526686419746540817 3332245895014814809905613)
  ·
    refine ⟨1249592210630555553714605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3332245895014814809905613 1249592210630555553714605)
    ·
      refine ⟨468597078986458332642977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1249592210630555553714605 468597078986458332642977)
      ·
        refine ⟨351447809239843749482233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 468597078986458332642977 351447809239843749482233)
        ·
          refine ⟨263585856929882812111675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351447809239843749482233 263585856929882812111675)
          ·
            refine ⟨395378785394824218167513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263585856929882812111675 395378785394824218167513)
            ·
              refine ⟨296534089046118163625635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395378785394824218167513 296534089046118163625635)
              ·
                refine ⟨444801133569177245438453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296534089046118163625635 444801133569177245438453)
                ·
                  refine ⟨41700106272110366759855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 444801133569177245438453 41700106272110366759855)
                  ·
                    rfl

theorem cell21_182724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_182724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_182724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_182724 prefixEnd_182724 := by exact prefixLift 182724
  have htrace : WordTrace (prefixWord ++ tailWord_182724) baseStart_182724 baseEnd_182724 := by
    simpa [prefixWord, tailWord_182724, baseEnd_182724] using wordTrace_append hprefix tailTrace_182724
  have hstable : (prefixWord ++ tailWord_182724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182724).length < 2 ^ (prefixWord ++ tailWord_182724).sum := by decide
  have hdescent : baseEnd_182724 < baseStart_182724 := by decide
  rcases family_descends (prefixWord ++ tailWord_182724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182963 : List Nat := [1, 1, 1, 2, 3, 5, 2, 6]
def baseStart_182963 : Nat := 118140960795 + 182963 * 2 ^ 59
def prefixEnd_182963 : Nat := 4983230072969 + 3 ^ 40 * 182963 * 2
def baseEnd_182963 : Nat := 13918216442766354092011

theorem tailTrace_182963 : CollatzResearch.WordTrace tailWord_182963 prefixEnd_182963 13918216442766354092011 := by
  unfold tailWord_182963
  simp only [CollatzResearch.WordTrace]
  refine ⟨6673208836163773437761543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4448805890775848958507695 6673208836163773437761543)
  ·
    refine ⟨10009813254245660156642315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6673208836163773437761543 10009813254245660156642315)
    ·
      refine ⟨15014719881368490234963473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10009813254245660156642315 15014719881368490234963473)
      ·
        refine ⟨11261039911026367676222605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15014719881368490234963473 11261039911026367676222605)
        ·
          refine ⟨4222889966634887878583477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11261039911026367676222605 4222889966634887878583477)
          ·
            refine ⟨395895934372020738617201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4222889966634887878583477 395895934372020738617201)
            ·
              refine ⟨296921950779015553962901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395895934372020738617201 296921950779015553962901)
              ·
                refine ⟨13918216442766354092011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 296921950779015553962901 13918216442766354092011)
                ·
                  rfl

theorem cell21_182963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 6].length) (baseStart_182963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_182963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_182963 prefixEnd_182963 := by exact prefixLift 182963
  have htrace : WordTrace (prefixWord ++ tailWord_182963) baseStart_182963 baseEnd_182963 := by
    simpa [prefixWord, tailWord_182963, baseEnd_182963] using wordTrace_append hprefix tailTrace_182963
  have hstable : (prefixWord ++ tailWord_182963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182963).length < 2 ^ (prefixWord ++ tailWord_182963).sum := by decide
  have hdescent : baseEnd_182963 < baseStart_182963 := by decide
  rcases family_descends (prefixWord ++ tailWord_182963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183132 : List Nat := [2, 2, 4, 2, 1, 2, 2, 6]
def baseStart_183132 : Nat := 118140960795 + 183132 * 2 ^ 59
def prefixEnd_183132 : Nat := 4983230072969 + 3 ^ 40 * 183132 * 2
def baseEnd_183132 : Nat := 13931072476930774653007

theorem tailTrace_183132 : CollatzResearch.WordTrace tailWord_183132 prefixEnd_183132 13931072476930774653007 := by
  unfold tailWord_183132
  simp only [CollatzResearch.WordTrace]
  refine ⟨3339686386275757650331825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4452915181701010200442433 3339686386275757650331825)
  ·
    refine ⟨2504764789706818237748869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3339686386275757650331825 2504764789706818237748869)
    ·
      refine ⟨469643398070028419577913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2504764789706818237748869 469643398070028419577913)
      ·
        refine ⟨352232548552521314683435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 469643398070028419577913 352232548552521314683435)
        ·
          refine ⟨528348822828781972025153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352232548552521314683435 528348822828781972025153)
          ·
            refine ⟨396261617121586479018865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 528348822828781972025153 396261617121586479018865)
            ·
              refine ⟨297196212841189859264149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396261617121586479018865 297196212841189859264149)
              ·
                refine ⟨13931072476930774653007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 297196212841189859264149 13931072476930774653007)
                ·
                  rfl

theorem cell21_183132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 6].length) (baseStart_183132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_183132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_183132 prefixEnd_183132 := by exact prefixLift 183132
  have htrace : WordTrace (prefixWord ++ tailWord_183132) baseStart_183132 baseEnd_183132 := by
    simpa [prefixWord, tailWord_183132, baseEnd_183132] using wordTrace_append hprefix tailTrace_183132
  have hstable : (prefixWord ++ tailWord_183132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183132).length < 2 ^ (prefixWord ++ tailWord_183132).sum := by decide
  have hdescent : baseEnd_183132 < baseStart_183132 := by decide
  rcases family_descends (prefixWord ++ tailWord_183132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183177 : List Nat := [1, 2, 1, 1, 5, 3, 2, 2, 4]
def baseStart_183177 : Nat := 118140960795 + 183177 * 2 ^ 59
def prefixEnd_183177 : Nat := 4983230072969 + 3 ^ 40 * 183177 * 2
def baseEnd_183177 : Nat := 41803487043882245708929

theorem tailTrace_183177 : CollatzResearch.WordTrace tailWord_183177 prefixEnd_183177 41803487043882245708929 := by
  unfold tailWord_183177
  simp only [CollatzResearch.WordTrace]
  refine ⟨6681014057388487986051785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4454009371592325324034523 6681014057388487986051785)
  ·
    refine ⟨5010760543041365989538839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6681014057388487986051785 5010760543041365989538839)
    ·
      refine ⟨7516140814562048984308259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5010760543041365989538839 7516140814562048984308259)
      ·
        refine ⟨11274211221843073476462389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7516140814562048984308259 11274211221843073476462389)
        ·
          refine ⟨1056957302047788138418349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11274211221843073476462389 1056957302047788138418349)
          ·
            refine ⟨396358988267920551906881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1056957302047788138418349 396358988267920551906881)
            ·
              refine ⟨297269241200940413930161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396358988267920551906881 297269241200940413930161)
              ·
                refine ⟨222951930900705310447621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297269241200940413930161 222951930900705310447621)
                ·
                  refine ⟨41803487043882245708929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 222951930900705310447621 41803487043882245708929)
                  ·
                    rfl

theorem cell21_183177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 4].length) (baseStart_183177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_183177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_183177 prefixEnd_183177 := by exact prefixLift 183177
  have htrace : WordTrace (prefixWord ++ tailWord_183177) baseStart_183177 baseEnd_183177 := by
    simpa [prefixWord, tailWord_183177, baseEnd_183177] using wordTrace_append hprefix tailTrace_183177
  have hstable : (prefixWord ++ tailWord_183177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183177).length < 2 ^ (prefixWord ++ tailWord_183177).sum := by decide
  have hdescent : baseEnd_183177 < baseStart_183177 := by decide
  rcases family_descends (prefixWord ++ tailWord_183177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183245 : List Nat := [1, 6, 3, 1, 1, 1, 3, 1, 4]
def baseStart_183245 : Nat := 118140960795 + 183245 * 2 ^ 59
def prefixEnd_183245 : Nat := 4983230072969 + 3 ^ 40 * 183245 * 2
def baseEnd_183245 : Nat := 41819005570329238575457

theorem tailTrace_183245 : CollatzResearch.WordTrace tailWord_183245 prefixEnd_183245 41819005570329238575457 := by
  unfold tailWord_183245
  simp only [CollatzResearch.WordTrace]
  refine ⟨6683494221142135599527189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4455662814094757066351459 6683494221142135599527189)
  ·
    refine ⟨313288791616037606227837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6683494221142135599527189 313288791616037606227837)
    ·
      refine ⟨117483296856014102335439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313288791616037606227837 117483296856014102335439)
      ·
        refine ⟨176224945284021153503159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117483296856014102335439 176224945284021153503159)
        ·
          refine ⟨264337417926031730254739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176224945284021153503159 264337417926031730254739)
          ·
            refine ⟨396506126889047595382109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264337417926031730254739 396506126889047595382109)
            ·
              refine ⟨148689797583392848268291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 396506126889047595382109 148689797583392848268291)
              ·
                refine ⟨223034696375089272402437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148689797583392848268291 223034696375089272402437)
                ·
                  refine ⟨41819005570329238575457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 223034696375089272402437 41819005570329238575457)
                  ·
                    rfl

theorem cell21_183245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_183245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_183245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_183245 prefixEnd_183245 := by exact prefixLift 183245
  have htrace : WordTrace (prefixWord ++ tailWord_183245) baseStart_183245 baseEnd_183245 := by
    simpa [prefixWord, tailWord_183245, baseEnd_183245] using wordTrace_append hprefix tailTrace_183245
  have hstable : (prefixWord ++ tailWord_183245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183245).length < 2 ^ (prefixWord ++ tailWord_183245).sum := by decide
  have hdescent : baseEnd_183245 < baseStart_183245 := by decide
  rcases family_descends (prefixWord ++ tailWord_183245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183388 : List Nat := [2, 2, 4, 1, 1, 1, 2, 2, 6]
def baseStart_183388 : Nat := 118140960795 + 183388 * 2 ^ 59
def prefixEnd_183388 : Nat := 4983230072969 + 3 ^ 40 * 183388 * 2
def baseEnd_183388 : Nat := 41851640118592767691831

theorem tailTrace_183388 : CollatzResearch.WordTrace tailWord_183388 prefixEnd_183388 41851640118592767691831 := by
  unfold tailWord_183388
  simp only [CollatzResearch.WordTrace]
  refine ⟨3344354929812035510991409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4459139906416047347988545 3344354929812035510991409)
  ·
    refine ⟨2508266197359026633243557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3344354929812035510991409 2508266197359026633243557)
    ·
      refine ⟨470299912004817493733167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2508266197359026633243557 470299912004817493733167)
      ·
        refine ⟨705449868007226240599751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470299912004817493733167 705449868007226240599751)
        ·
          refine ⟨1058174802010839360899627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 705449868007226240599751 1058174802010839360899627)
          ·
            refine ⟨1587262203016259041349441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058174802010839360899627 1587262203016259041349441)
            ·
              refine ⟨1190446652262194281012081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1587262203016259041349441 1190446652262194281012081)
              ·
                refine ⟨892834989196645710759061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1190446652262194281012081 892834989196645710759061)
                ·
                  refine ⟨41851640118592767691831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 892834989196645710759061 41851640118592767691831)
                  ·
                    rfl

theorem cell21_183388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_183388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_183388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_183388 prefixEnd_183388 := by exact prefixLift 183388
  have htrace : WordTrace (prefixWord ++ tailWord_183388) baseStart_183388 baseEnd_183388 := by
    simpa [prefixWord, tailWord_183388, baseEnd_183388] using wordTrace_append hprefix tailTrace_183388
  have hstable : (prefixWord ++ tailWord_183388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183388).length < 2 ^ (prefixWord ++ tailWord_183388).sum := by decide
  have hdescent : baseEnd_183388 < baseStart_183388 := by decide
  rcases family_descends (prefixWord ++ tailWord_183388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183405 : List Nat := [1, 5, 1, 1, 2, 2, 3, 2, 4]
def baseStart_183405 : Nat := 118140960795 + 183405 * 2 ^ 59
def prefixEnd_183405 : Nat := 4983230072969 + 3 ^ 40 * 183405 * 2
def baseEnd_183405 : Nat := 41855519750204515908463

theorem tailTrace_183405 : CollatzResearch.WordTrace tailWord_183405 prefixEnd_183405 41855519750204515908463 := by
  unfold tailWord_183405
  simp only [CollatzResearch.WordTrace]
  refine ⟨6689329900562482925351669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4459553267041655283567779 6689329900562482925351669)
  ·
    refine ⟨627124678177732774251719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6689329900562482925351669 627124678177732774251719)
    ·
      refine ⟨940687017266599161377579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 627124678177732774251719 940687017266599161377579)
      ·
        refine ⟨1411030525899898742066369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 940687017266599161377579 1411030525899898742066369)
        ·
          refine ⟨1058272894424924056549777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1411030525899898742066369 1058272894424924056549777)
          ·
            refine ⟨793704670818693042412333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1058272894424924056549777 793704670818693042412333)
            ·
              refine ⟨297639251557009890904625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 793704670818693042412333 297639251557009890904625)
              ·
                refine ⟨223229438667757418178469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297639251557009890904625 223229438667757418178469)
                ·
                  refine ⟨41855519750204515908463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 223229438667757418178469 41855519750204515908463)
                  ·
                    rfl

theorem cell21_183405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_183405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_183405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_183405 prefixEnd_183405 := by exact prefixLift 183405
  have htrace : WordTrace (prefixWord ++ tailWord_183405) baseStart_183405 baseEnd_183405 := by
    simpa [prefixWord, tailWord_183405, baseEnd_183405] using wordTrace_append hprefix tailTrace_183405
  have hstable : (prefixWord ++ tailWord_183405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183405).length < 2 ^ (prefixWord ++ tailWord_183405).sum := by decide
  have hdescent : baseEnd_183405 < baseStart_183405 := by decide
  rcases family_descends (prefixWord ++ tailWord_183405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183433 : List Nat := [1, 2, 1, 1, 4, 3, 2, 2, 5]
def baseStart_183433 : Nat := 118140960795 + 183433 * 2 ^ 59
def prefixEnd_183433 : Nat := 4983230072969 + 3 ^ 40 * 183433 * 2
def baseEnd_183433 : Nat := 41861909731682689441739

theorem tailTrace_183433 : CollatzResearch.WordTrace tailWord_183433 prefixEnd_183433 41861909731682689441739 := by
  unfold tailWord_183433
  simp only [CollatzResearch.WordTrace]
  refine ⟨6690351144461043707370953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4460234096307362471580635 6690351144461043707370953)
  ·
    refine ⟨5017763358345782780528215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6690351144461043707370953 5017763358345782780528215)
    ·
      refine ⟨7526645037518674170792323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5017763358345782780528215 7526645037518674170792323)
      ·
        refine ⟨11289967556278011256188485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7526645037518674170792323 11289967556278011256188485)
        ·
          refine ⟨2116868916802127110535341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11289967556278011256188485 2116868916802127110535341)
          ·
            refine ⟨793825843800797666450753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2116868916802127110535341 793825843800797666450753)
            ·
              refine ⟨595369382850598249838065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 793825843800797666450753 595369382850598249838065)
              ·
                refine ⟨446527037137948687378549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 595369382850598249838065 446527037137948687378549)
                ·
                  refine ⟨41861909731682689441739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 446527037137948687378549 41861909731682689441739)
                  ·
                    rfl

theorem cell21_183433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 5].length) (baseStart_183433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_183433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_183433 prefixEnd_183433 := by exact prefixLift 183433
  have htrace : WordTrace (prefixWord ++ tailWord_183433) baseStart_183433 baseEnd_183433 := by
    simpa [prefixWord, tailWord_183433, baseEnd_183433] using wordTrace_append hprefix tailTrace_183433
  have hstable : (prefixWord ++ tailWord_183433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183433).length < 2 ^ (prefixWord ++ tailWord_183433).sum := by decide
  have hdescent : baseEnd_183433 < baseStart_183433 := by decide
  rcases family_descends (prefixWord ++ tailWord_183433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183481 : List Nat := [1, 2, 1, 4, 1, 3, 4, 1, 4]
def baseStart_183481 : Nat := 118140960795 + 183481 * 2 ^ 59
def prefixEnd_183481 : Nat := 4983230072969 + 3 ^ 40 * 183481 * 2
def baseEnd_183481 : Nat := 41872863985645272641641

theorem tailTrace_183481 : CollatzResearch.WordTrace tailWord_183481 prefixEnd_183481 41872863985645272641641 := by
  unfold tailWord_183481
  simp only [CollatzResearch.WordTrace]
  refine ⟨6692101848287147905118297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4461401232191431936745531 6692101848287147905118297)
  ·
    refine ⟨5019076386215360928838723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6692101848287147905118297 5019076386215360928838723)
    ·
      refine ⟨7528614579323041393258085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5019076386215360928838723 7528614579323041393258085)
      ·
        refine ⟨1411615233623070261235891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7528614579323041393258085 1411615233623070261235891)
        ·
          refine ⟨2117422850434605391853837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1411615233623070261235891 2117422850434605391853837)
          ·
            refine ⟨794033568912977021945189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2117422850434605391853837 794033568912977021945189)
            ·
              refine ⟨148881294171183191614723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 794033568912977021945189 148881294171183191614723)
              ·
                refine ⟨223321941256774787422085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148881294171183191614723 223321941256774787422085)
                ·
                  refine ⟨41872863985645272641641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 223321941256774787422085 41872863985645272641641)
                  ·
                    rfl

theorem cell21_183481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 4].length) (baseStart_183481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_183481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_183481 prefixEnd_183481 := by exact prefixLift 183481
  have htrace : WordTrace (prefixWord ++ tailWord_183481) baseStart_183481 baseEnd_183481 := by
    simpa [prefixWord, tailWord_183481, baseEnd_183481] using wordTrace_append hprefix tailTrace_183481
  have hstable : (prefixWord ++ tailWord_183481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183481).length < 2 ^ (prefixWord ++ tailWord_183481).sum := by decide
  have hdescent : baseEnd_183481 < baseStart_183481 := by decide
  rcases family_descends (prefixWord ++ tailWord_183481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183622 : List Nat := [6, 1, 1, 3, 2, 1, 7]
def baseStart_183622 : Nat := 118140960795 + 183622 * 2 ^ 59
def prefixEnd_183622 : Nat := 4983230072969 + 3 ^ 40 * 183622 * 2
def baseEnd_183622 : Nat := 4656115789628928976817

theorem tailTrace_183622 : CollatzResearch.WordTrace tailWord_183622 prefixEnd_183622 4656115789628928976817 := by
  unfold tailWord_183622
  simp only [CollatzResearch.WordTrace]
  refine ⟨209288891899260280812535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4464829693850885990667413 209288891899260280812535)
  ·
    refine ⟨313933337848890421218803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209288891899260280812535 313933337848890421218803)
    ·
      refine ⟨470900006773335631828205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313933337848890421218803 470900006773335631828205)
      ·
        refine ⟨176587502540000861935577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 470900006773335631828205 176587502540000861935577)
        ·
          refine ⟨132440626905000646451683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176587502540000861935577 132440626905000646451683)
          ·
            refine ⟨198660940357500969677525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132440626905000646451683 198660940357500969677525)
            ·
              refine ⟨4656115789628928976817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 198660940357500969677525 4656115789628928976817)
              ·
                rfl

theorem cell21_183622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 7].length) (baseStart_183622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_183622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_183622 prefixEnd_183622 := by exact prefixLift 183622
  have htrace : WordTrace (prefixWord ++ tailWord_183622) baseStart_183622 baseEnd_183622 := by
    simpa [prefixWord, tailWord_183622, baseEnd_183622] using wordTrace_append hprefix tailTrace_183622
  have hstable : (prefixWord ++ tailWord_183622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183622).length < 2 ^ (prefixWord ++ tailWord_183622).sum := by decide
  have hdescent : baseEnd_183622 < baseStart_183622 := by decide
  rcases family_descends (prefixWord ++ tailWord_183622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183689 : List Nat := [1, 2, 1, 1, 16]
def baseStart_183689 : Nat := 118140960795 + 183689 * 2 ^ 59
def prefixEnd_183689 : Nat := 4983230072969 + 3 ^ 40 * 183689 * 2
def baseEnd_183689 : Nat := 517534968141767076229

theorem tailTrace_183689 : CollatzResearch.WordTrace tailWord_183689 prefixEnd_183689 517534968141767076229 := by
  unfold tailWord_183689
  simp only [CollatzResearch.WordTrace]
  refine ⟨6699688231533599428690121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4466458821022399619126747 6699688231533599428690121)
  ·
    refine ⟨5024766173650199571517591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6699688231533599428690121 5024766173650199571517591)
    ·
      refine ⟨7537149260475299357276387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5024766173650199571517591 7537149260475299357276387)
      ·
        refine ⟨11305723890712949035914581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7537149260475299357276387 11305723890712949035914581)
        ·
          refine ⟨517534968141767076229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 11305723890712949035914581 517534968141767076229)
          ·
            rfl

theorem cell21_183689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 16].length) (baseStart_183689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_183689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_183689 prefixEnd_183689 := by exact prefixLift 183689
  have htrace : WordTrace (prefixWord ++ tailWord_183689) baseStart_183689 baseEnd_183689 := by
    simpa [prefixWord, tailWord_183689, baseEnd_183689] using wordTrace_append hprefix tailTrace_183689
  have hstable : (prefixWord ++ tailWord_183689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183689).length < 2 ^ (prefixWord ++ tailWord_183689).sum := by decide
  have hdescent : baseEnd_183689 < baseStart_183689 := by decide
  rcases family_descends (prefixWord ++ tailWord_183689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183692 : List Nat := [2, 2, 1, 2, 1, 3, 4, 2, 4]
def baseStart_183692 : Nat := 118140960795 + 183692 * 2 ^ 59
def prefixEnd_183692 : Nat := 4983230072969 + 3 ^ 40 * 183692 * 2
def baseEnd_183692 : Nat := 41921017060355794624543

theorem tailTrace_183692 : CollatzResearch.WordTrace tailWord_183692 prefixEnd_183692 41921017060355794624543 := by
  unfold tailWord_183692
  simp only [CollatzResearch.WordTrace]
  refine ⟨3349898825261365470524665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4466531767015153960699553 3349898825261365470524665)
  ·
    refine ⟨2512424118946024102893499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3349898825261365470524665 2512424118946024102893499)
    ·
      refine ⟨3768636178419036154340249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2512424118946024102893499 3768636178419036154340249)
      ·
        refine ⟨2826477133814277115755187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3768636178419036154340249 2826477133814277115755187)
        ·
          refine ⟨4239715700721415673632781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2826477133814277115755187 4239715700721415673632781)
          ·
            refine ⟨1589893387770530877612293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4239715700721415673632781 1589893387770530877612293)
            ·
              refine ⟨298105010206974539552305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1589893387770530877612293 298105010206974539552305)
              ·
                refine ⟨223578757655230904664229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298105010206974539552305 223578757655230904664229)
                ·
                  refine ⟨41921017060355794624543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 223578757655230904664229 41921017060355794624543)
                  ·
                    rfl

theorem cell21_183692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_183692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_183692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_183692 prefixEnd_183692 := by exact prefixLift 183692
  have htrace : WordTrace (prefixWord ++ tailWord_183692) baseStart_183692 baseEnd_183692 := by
    simpa [prefixWord, tailWord_183692, baseEnd_183692] using wordTrace_append hprefix tailTrace_183692
  have hstable : (prefixWord ++ tailWord_183692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183692).length < 2 ^ (prefixWord ++ tailWord_183692).sum := by decide
  have hdescent : baseEnd_183692 < baseStart_183692 := by decide
  rcases family_descends (prefixWord ++ tailWord_183692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183751 : List Nat := [1, 1, 4, 1, 1, 3, 3, 1, 6]
def baseStart_183751 : Nat := 118140960795 + 183751 * 2 ^ 59
def prefixEnd_183751 : Nat := 4983230072969 + 3 ^ 40 * 183751 * 2
def baseEnd_183751 : Nat := 41934481664184803141089

theorem tailTrace_183751 : CollatzResearch.WordTrace tailWord_183751 prefixEnd_183751 41934481664184803141089 := by
  unfold tailWord_183751
  simp only [CollatzResearch.WordTrace]
  refine ⟨6701949557308984017447107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4467966371539322678298071 6701949557308984017447107)
  ·
    refine ⟨10052924335963476026170661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6701949557308984017447107 10052924335963476026170661)
    ·
      refine ⟨1884923312993151754906999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10052924335963476026170661 1884923312993151754906999)
      ·
        refine ⟨2827384969489727632360499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1884923312993151754906999 2827384969489727632360499)
        ·
          refine ⟨4241077454234591448540749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2827384969489727632360499 4241077454234591448540749)
          ·
            refine ⟨1590404045337971793202781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4241077454234591448540749 1590404045337971793202781)
            ·
              refine ⟨596401517001739422451043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1590404045337971793202781 596401517001739422451043)
              ·
                refine ⟨894602275502609133676565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 596401517001739422451043 894602275502609133676565)
                ·
                  refine ⟨41934481664184803141089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 894602275502609133676565 41934481664184803141089)
                  ·
                    rfl

theorem cell21_183751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 6].length) (baseStart_183751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_183751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_183751 prefixEnd_183751 := by exact prefixLift 183751
  have htrace : WordTrace (prefixWord ++ tailWord_183751) baseStart_183751 baseEnd_183751 := by
    simpa [prefixWord, tailWord_183751, baseEnd_183751] using wordTrace_append hprefix tailTrace_183751
  have hstable : (prefixWord ++ tailWord_183751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183751).length < 2 ^ (prefixWord ++ tailWord_183751).sum := by decide
  have hdescent : baseEnd_183751 < baseStart_183751 := by decide
  rcases family_descends (prefixWord ++ tailWord_183751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183754 : List Nat := [3, 1, 2, 1, 2, 3, 2, 4, 3]
def baseStart_183754 : Nat := 118140960795 + 183754 * 2 ^ 59
def prefixEnd_183754 : Nat := 4983230072969 + 3 ^ 40 * 183754 * 2
def baseEnd_183754 : Nat := 41935166305057464591083

theorem tailTrace_183754 : CollatzResearch.WordTrace tailWord_183754 prefixEnd_183754 41935166305057464591083 := by
  unfold tailWord_183754
  simp only [CollatzResearch.WordTrace]
  refine ⟨1675514744074528882451579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4468039317532077019870877 1675514744074528882451579)
  ·
    refine ⟨2513272116111793323677369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1675514744074528882451579 2513272116111793323677369)
    ·
      refine ⟨1884954087083844992758027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2513272116111793323677369 1884954087083844992758027)
      ·
        refine ⟨2827431130625767489137041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1884954087083844992758027 2827431130625767489137041)
        ·
          refine ⟨2120573347969325616852781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2827431130625767489137041 2120573347969325616852781)
          ·
            refine ⟨795215005488497106319793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2120573347969325616852781 795215005488497106319793)
            ·
              refine ⟨596411254116372829739845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 795215005488497106319793 596411254116372829739845)
              ·
                refine ⟨111827110146819905576221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 596411254116372829739845 111827110146819905576221)
                ·
                  refine ⟨41935166305057464591083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111827110146819905576221 41935166305057464591083)
                  ·
                    rfl

theorem cell21_183754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4, 3].length) (baseStart_183754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_183754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_183754 prefixEnd_183754 := by exact prefixLift 183754
  have htrace : WordTrace (prefixWord ++ tailWord_183754) baseStart_183754 baseEnd_183754 := by
    simpa [prefixWord, tailWord_183754, baseEnd_183754] using wordTrace_append hprefix tailTrace_183754
  have hstable : (prefixWord ++ tailWord_183754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183754).length < 2 ^ (prefixWord ++ tailWord_183754).sum := by decide
  have hdescent : baseEnd_183754 < baseStart_183754 := by decide
  rcases family_descends (prefixWord ++ tailWord_183754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183872 : List Nat := [2, 1, 1, 2, 2, 2, 1, 5, 5]
def baseStart_183872 : Nat := 118140960795 + 183872 * 2 ^ 59
def prefixEnd_183872 : Nat := 4983230072969 + 3 ^ 40 * 183872 * 2
def baseEnd_183872 : Nat := 41962095512715481624175

theorem tailTrace_183872 : CollatzResearch.WordTrace tailWord_183872 prefixEnd_183872 41962095512715481624175 := by
  unfold tailWord_183872
  simp only [CollatzResearch.WordTrace]
  refine ⟨3353181394935310841300935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4470908526580414455067913 3353181394935310841300935)
  ·
    refine ⟨5029772092402966261951403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3353181394935310841300935 5029772092402966261951403)
    ·
      refine ⟨7544658138604449392927105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5029772092402966261951403 7544658138604449392927105)
      ·
        refine ⟨5658493603953337044695329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7544658138604449392927105 5658493603953337044695329)
        ·
          refine ⟨4243870202965002783521497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5658493603953337044695329 4243870202965002783521497)
          ·
            refine ⟨3182902652223752087641123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4243870202965002783521497 3182902652223752087641123)
            ·
              refine ⟨4774353978335628131461685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3182902652223752087641123 4774353978335628131461685)
              ·
                refine ⟨447595685468965137324533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4774353978335628131461685 447595685468965137324533)
                ·
                  refine ⟨41962095512715481624175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 447595685468965137324533 41962095512715481624175)
                  ·
                    rfl

theorem cell21_183872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 5].length) (baseStart_183872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_183872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_183872 prefixEnd_183872 := by exact prefixLift 183872
  have htrace : WordTrace (prefixWord ++ tailWord_183872) baseStart_183872 baseEnd_183872 := by
    simpa [prefixWord, tailWord_183872, baseEnd_183872] using wordTrace_append hprefix tailTrace_183872
  have hstable : (prefixWord ++ tailWord_183872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183872).length < 2 ^ (prefixWord ++ tailWord_183872).sum := by decide
  have hdescent : baseEnd_183872 < baseStart_183872 := by decide
  rcases family_descends (prefixWord ++ tailWord_183872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183920 : List Nat := [2, 1, 1, 1, 6, 1, 3, 2, 4]
def baseStart_183920 : Nat := 118140960795 + 183920 * 2 ^ 59
def prefixEnd_183920 : Nat := 4983230072969 + 3 ^ 40 * 183920 * 2
def baseEnd_183920 : Nat := 41973049766678064824077

theorem tailTrace_183920 : CollatzResearch.WordTrace tailWord_183920 prefixEnd_183920 41973049766678064824077 := by
  unfold tailWord_183920
  simp only [CollatzResearch.WordTrace]
  refine ⟨3354056746848362940174607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4472075662464483920232809 3354056746848362940174607)
  ·
    refine ⟨5031085120272544410261911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3354056746848362940174607 5031085120272544410261911)
    ·
      refine ⟨7546627680408816615392867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5031085120272544410261911 7546627680408816615392867)
      ·
        refine ⟨11319941520613224923089301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7546627680408816615392867 11319941520613224923089301)
        ·
          refine ⟨530622258778744918269811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11319941520613224923089301 530622258778744918269811)
          ·
            refine ⟨795933388168117377404717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530622258778744918269811 795933388168117377404717)
            ·
              refine ⟨298475020563044016526769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 795933388168117377404717 298475020563044016526769)
              ·
                refine ⟨223856265422283012395077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298475020563044016526769 223856265422283012395077)
                ·
                  refine ⟨41973049766678064824077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 223856265422283012395077 41973049766678064824077)
                  ·
                    rfl

theorem cell21_183920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 4].length) (baseStart_183920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_183920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_183920 prefixEnd_183920 := by exact prefixLift 183920
  have htrace : WordTrace (prefixWord ++ tailWord_183920) baseStart_183920 baseEnd_183920 := by
    simpa [prefixWord, tailWord_183920, baseEnd_183920] using wordTrace_append hprefix tailTrace_183920
  have hstable : (prefixWord ++ tailWord_183920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183920).length < 2 ^ (prefixWord ++ tailWord_183920).sum := by decide
  have hdescent : baseEnd_183920 < baseStart_183920 := by decide
  rcases family_descends (prefixWord ++ tailWord_183920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183937 : List Nat := [1, 2, 4, 2, 1, 3, 3, 1, 4]
def baseStart_183937 : Nat := 118140960795 + 183937 * 2 ^ 59
def prefixEnd_183937 : Nat := 4983230072969 + 3 ^ 40 * 183937 * 2
def baseEnd_183937 : Nat := 41976929398289813040709

theorem tailTrace_183937 : CollatzResearch.WordTrace tailWord_183937 prefixEnd_183937 41976929398289813040709 := by
  unfold tailWord_183937
  simp only [CollatzResearch.WordTrace]
  refine ⟨6708733534635137783718065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4472489023090091855812043 6708733534635137783718065)
  ·
    refine ⟨5031550150976353337788549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6708733534635137783718065 5031550150976353337788549)
    ·
      refine ⟨943415653308066250835353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5031550150976353337788549 943415653308066250835353)
      ·
        refine ⟨707561739981049688126515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 943415653308066250835353 707561739981049688126515)
        ·
          refine ⟨1061342609971574532189773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707561739981049688126515 1061342609971574532189773)
          ·
            refine ⟨398003478739340449571165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1061342609971574532189773 398003478739340449571165)
            ·
              refine ⟨149251304527252668589187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 398003478739340449571165 149251304527252668589187)
              ·
                refine ⟨223876956790879002883781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149251304527252668589187 223876956790879002883781)
                ·
                  refine ⟨41976929398289813040709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 223876956790879002883781 41976929398289813040709)
                  ·
                    rfl

theorem cell21_183937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 4].length) (baseStart_183937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_183937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_183937 prefixEnd_183937 := by exact prefixLift 183937
  have htrace : WordTrace (prefixWord ++ tailWord_183937) baseStart_183937 baseEnd_183937 := by
    simpa [prefixWord, tailWord_183937, baseEnd_183937] using wordTrace_append hprefix tailTrace_183937
  have hstable : (prefixWord ++ tailWord_183937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183937).length < 2 ^ (prefixWord ++ tailWord_183937).sum := by decide
  have hdescent : baseEnd_183937 < baseStart_183937 := by decide
  rcases family_descends (prefixWord ++ tailWord_183937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183948 : List Nat := [2, 2, 1, 2, 1, 1, 3, 4, 5]
def baseStart_183948 : Nat := 118140960795 + 183948 * 2 ^ 59
def prefixEnd_183948 : Nat := 4983230072969 + 3 ^ 40 * 183948 * 2
def baseEnd_183948 : Nat := 41979439748156238357353

theorem tailTrace_183948 : CollatzResearch.WordTrace tailWord_183948 prefixEnd_183948 41979439748156238357353 := by
  unfold tailWord_183948
  simp only [CollatzResearch.WordTrace]
  refine ⟨3354567368797643331184249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4472756491730191108245665 3354567368797643331184249)
  ·
    refine ⟨2515925526598232498388187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3354567368797643331184249 2515925526598232498388187)
    ·
      refine ⟨3773888289897348747582281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2515925526598232498388187 3773888289897348747582281)
      ·
        refine ⟨2830416217423011560686711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3773888289897348747582281 2830416217423011560686711)
        ·
          refine ⟨4245624326134517341030067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2830416217423011560686711 4245624326134517341030067)
          ·
            refine ⟨6368436489201776011545101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4245624326134517341030067 6368436489201776011545101)
            ·
              refine ⟨2388163683450666004329413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6368436489201776011545101 2388163683450666004329413)
              ·
                refine ⟨447780690646999875811765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2388163683450666004329413 447780690646999875811765)
                ·
                  refine ⟨41979439748156238357353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 447780690646999875811765 41979439748156238357353)
                  ·
                    rfl

theorem cell21_183948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_183948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_183948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_183948 prefixEnd_183948 := by exact prefixLift 183948
  have htrace : WordTrace (prefixWord ++ tailWord_183948) baseStart_183948 baseEnd_183948 := by
    simpa [prefixWord, tailWord_183948, baseEnd_183948] using wordTrace_append hprefix tailTrace_183948
  have hstable : (prefixWord ++ tailWord_183948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183948).length < 2 ^ (prefixWord ++ tailWord_183948).sum := by decide
  have hdescent : baseEnd_183948 < baseStart_183948 := by decide
  rcases family_descends (prefixWord ++ tailWord_183948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183993 : List Nat := [1, 2, 1, 4, 1, 1, 3, 8]
def baseStart_183993 : Nat := 118140960795 + 183993 * 2 ^ 59
def prefixEnd_183993 : Nat := 4983230072969 + 3 ^ 40 * 183993 * 2
def baseEnd_183993 : Nat := 13996569787082053369087

theorem tailTrace_183993 : CollatzResearch.WordTrace tailWord_183993 prefixEnd_183993 13996569787082053369087 := by
  unfold tailWord_183993
  simp only [CollatzResearch.WordTrace]
  refine ⟨6710776022432259347756633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4473850681621506231837755 6710776022432259347756633)
  ·
    refine ⟨5033082016824194510817475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6710776022432259347756633 5033082016824194510817475)
    ·
      refine ⟨7549623025236291766226213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5033082016824194510817475 7549623025236291766226213)
      ·
        refine ⟨1415554317231804706167415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7549623025236291766226213 1415554317231804706167415)
        ·
          refine ⟨2123331475847707059251123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1415554317231804706167415 2123331475847707059251123)
          ·
            refine ⟨3184997213771560588876685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2123331475847707059251123 3184997213771560588876685)
            ·
              refine ⟨1194373955164335220828757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3184997213771560588876685 1194373955164335220828757)
              ·
                refine ⟨13996569787082053369087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1194373955164335220828757 13996569787082053369087)
                ·
                  rfl

theorem cell21_183993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 8].length) (baseStart_183993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_183993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_183993 prefixEnd_183993 := by exact prefixLift 183993
  have htrace : WordTrace (prefixWord ++ tailWord_183993) baseStart_183993 baseEnd_183993 := by
    simpa [prefixWord, tailWord_183993, baseEnd_183993] using wordTrace_append hprefix tailTrace_183993
  have hstable : (prefixWord ++ tailWord_183993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183993).length < 2 ^ (prefixWord ++ tailWord_183993).sum := by decide
  have hdescent : baseEnd_183993 < baseStart_183993 := by decide
  rcases family_descends (prefixWord ++ tailWord_183993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183996 : List Nat := [2, 2, 2, 3, 1, 3, 1, 3, 4]
def baseStart_183996 : Nat := 118140960795 + 183996 * 2 ^ 59
def prefixEnd_183996 : Nat := 4983230072969 + 3 ^ 40 * 183996 * 2
def baseEnd_183996 : Nat := 41990394002118821557255

theorem tailTrace_183996 : CollatzResearch.WordTrace tailWord_183996 prefixEnd_183996 41990394002118821557255 := by
  unfold tailWord_183996
  simp only [CollatzResearch.WordTrace]
  refine ⟨3355442720710695430057921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4473923627614260573410561 3355442720710695430057921)
  ·
    refine ⟨2516582040533021572543441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3355442720710695430057921 2516582040533021572543441)
    ·
      refine ⟨1887436530399766179407581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2516582040533021572543441 1887436530399766179407581)
      ·
        refine ⟨707788698899912317277843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1887436530399766179407581 707788698899912317277843)
        ·
          refine ⟨1061683048349868475916765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707788698899912317277843 1061683048349868475916765)
          ·
            refine ⟨398131143131200678468787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1061683048349868475916765 398131143131200678468787)
            ·
              refine ⟨597196714696801017703181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398131143131200678468787 597196714696801017703181)
              ·
                refine ⟨223948768011300381638693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 597196714696801017703181 223948768011300381638693)
                ·
                  refine ⟨41990394002118821557255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 223948768011300381638693 41990394002118821557255)
                  ·
                    rfl

theorem cell21_183996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_183996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_183996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_183996 prefixEnd_183996 := by exact prefixLift 183996
  have htrace : WordTrace (prefixWord ++ tailWord_183996) baseStart_183996 baseEnd_183996 := by
    simpa [prefixWord, tailWord_183996, baseEnd_183996] using wordTrace_append hprefix tailTrace_183996
  have hstable : (prefixWord ++ tailWord_183996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183996).length < 2 ^ (prefixWord ++ tailWord_183996).sum := by decide
  have hdescent : baseEnd_183996 < baseStart_183996 := by decide
  rcases family_descends (prefixWord ++ tailWord_183996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184055 : List Nat := [1, 1, 3, 1, 1, 1, 6, 3, 4]
def baseStart_184055 : Nat := 118140960795 + 184055 * 2 ^ 59
def prefixEnd_184055 : Nat := 4983230072969 + 3 ^ 40 * 184055 * 2
def baseEnd_184055 : Nat := 42003858605947830073801

theorem tailTrace_184055 : CollatzResearch.WordTrace tailWord_184055 prefixEnd_184055 42003858605947830073801 := by
  unfold tailWord_184055
  simp only [CollatzResearch.WordTrace]
  refine ⟨6713037348207643936513619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4475358232138429291009079 6713037348207643936513619)
  ·
    refine ⟨10069556022311465904770429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6713037348207643936513619 10069556022311465904770429)
    ·
      refine ⟨3776083508366799714288911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10069556022311465904770429 3776083508366799714288911)
      ·
        refine ⟨5664125262550199571433367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3776083508366799714288911 5664125262550199571433367)
        ·
          refine ⟨8496187893825299357150051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5664125262550199571433367 8496187893825299357150051)
          ·
            refine ⟨12744281840737949035725077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8496187893825299357150051 12744281840737949035725077)
            ·
              refine ⟨597388211284591361049613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12744281840737949035725077 597388211284591361049613)
              ·
                refine ⟨224020579231721760393605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 597388211284591361049613 224020579231721760393605)
                ·
                  refine ⟨42003858605947830073801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 224020579231721760393605 42003858605947830073801)
                  ·
                    rfl

theorem cell21_184055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 4].length) (baseStart_184055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_184055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_184055 prefixEnd_184055 := by exact prefixLift 184055
  have htrace : WordTrace (prefixWord ++ tailWord_184055) baseStart_184055 baseEnd_184055 := by
    simpa [prefixWord, tailWord_184055, baseEnd_184055] using wordTrace_append hprefix tailTrace_184055
  have hstable : (prefixWord ++ tailWord_184055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184055).length < 2 ^ (prefixWord ++ tailWord_184055).sum := by decide
  have hdescent : baseEnd_184055 < baseStart_184055 := by decide
  rcases family_descends (prefixWord ++ tailWord_184055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184145 : List Nat := [1, 2, 2, 1, 5, 1, 9]
def baseStart_184145 : Nat := 118140960795 + 184145 * 2 ^ 59
def prefixEnd_184145 : Nat := 4983230072969 + 3 ^ 40 * 184145 * 2
def baseEnd_184145 : Nat := 4669377536903074841513

theorem tailTrace_184145 : CollatzResearch.WordTrace tailWord_184145 prefixEnd_184145 4669377536903074841513 := by
  unfold tailWord_184145
  simp only [CollatzResearch.WordTrace]
  refine ⟨6716319917881589307289889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4477546611921059538193259 6716319917881589307289889)
  ·
    refine ⟨5037239938411191980467417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6716319917881589307289889 5037239938411191980467417)
    ·
      refine ⟨3777929953808393985350563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5037239938411191980467417 3777929953808393985350563)
      ·
        refine ⟨5666894930712590978025845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3777929953808393985350563 5666894930712590978025845)
        ·
          refine ⟨531271399754305404189923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5666894930712590978025845 531271399754305404189923)
          ·
            refine ⟨796907099631458106284885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531271399754305404189923 796907099631458106284885)
            ·
              refine ⟨4669377536903074841513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 796907099631458106284885 4669377536903074841513)
              ·
                rfl

theorem cell21_184145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 9].length) (baseStart_184145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_184145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_184145 prefixEnd_184145 := by exact prefixLift 184145
  have htrace : WordTrace (prefixWord ++ tailWord_184145) baseStart_184145 baseEnd_184145 := by
    simpa [prefixWord, tailWord_184145, baseEnd_184145] using wordTrace_append hprefix tailTrace_184145
  have hstable : (prefixWord ++ tailWord_184145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184145).length < 2 ^ (prefixWord ++ tailWord_184145).sum := by decide
  have hdescent : baseEnd_184145 < baseStart_184145 := by decide
  rcases family_descends (prefixWord ++ tailWord_184145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184151 : List Nat := [1, 1, 3, 2, 5, 1, 3, 2, 3]
def baseStart_184151 : Nat := 118140960795 + 184151 * 2 ^ 59
def prefixEnd_184151 : Nat := 4983230072969 + 3 ^ 40 * 184151 * 2
def baseEnd_184151 : Nat := 42025767113872996473605

theorem tailTrace_184151 : CollatzResearch.WordTrace tailWord_184151 prefixEnd_184151 42025767113872996473605 := by
  unfold tailWord_184151
  simp only [CollatzResearch.WordTrace]
  refine ⟨6716538755859852332008307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4477692503906568221338871 6716538755859852332008307)
  ·
    refine ⟨10074808133789778498012461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6716538755859852332008307 10074808133789778498012461)
    ·
      refine ⟨3778053050171166936754673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10074808133789778498012461 3778053050171166936754673)
      ·
        refine ⟨2833539787628375202566005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3778053050171166936754673 2833539787628375202566005)
        ·
          refine ⟨265644355090160175240563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2833539787628375202566005 265644355090160175240563)
          ·
            refine ⟨398466532635240262860845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265644355090160175240563 398466532635240262860845)
            ·
              refine ⟨149424949738215098572817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 398466532635240262860845 149424949738215098572817)
              ·
                refine ⟨112068712303661323929613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149424949738215098572817 112068712303661323929613)
                ·
                  refine ⟨42025767113872996473605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112068712303661323929613 42025767113872996473605)
                  ·
                    rfl

theorem cell21_184151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2, 3].length) (baseStart_184151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_184151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_184151 prefixEnd_184151 := by exact prefixLift 184151
  have htrace : WordTrace (prefixWord ++ tailWord_184151) baseStart_184151 baseEnd_184151 := by
    simpa [prefixWord, tailWord_184151, baseEnd_184151] using wordTrace_append hprefix tailTrace_184151
  have hstable : (prefixWord ++ tailWord_184151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184151).length < 2 ^ (prefixWord ++ tailWord_184151).sum := by decide
  have hdescent : baseEnd_184151 < baseStart_184151 := by decide
  rcases family_descends (prefixWord ++ tailWord_184151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184162 : List Nat := [3, 3, 2, 1, 2, 1, 1, 8]
def baseStart_184162 : Nat := 118140960795 + 184162 * 2 ^ 59
def prefixEnd_184162 : Nat := 4983230072969 + 3 ^ 40 * 184162 * 2
def baseEnd_184162 : Nat := 14009425821246473930083

theorem tailTrace_184162 : CollatzResearch.WordTrace tailWord_184162 prefixEnd_184162 14009425821246473930083 := by
  unfold tailWord_184162
  simp only [CollatzResearch.WordTrace]
  refine ⟨1679234989705000302664685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4477959972546667473772493 1679234989705000302664685)
  ·
    refine ⟨629713121139375113499257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1679234989705000302664685 629713121139375113499257)
    ·
      refine ⟨472284840854531335124443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 629713121139375113499257 472284840854531335124443)
      ·
        refine ⟨708427261281797002686665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472284840854531335124443 708427261281797002686665)
        ·
          refine ⟨531320445961347752014999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 708427261281797002686665 531320445961347752014999)
          ·
            refine ⟨796980668942021628022499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531320445961347752014999 796980668942021628022499)
            ·
              refine ⟨1195471003413032442033749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796980668942021628022499 1195471003413032442033749)
              ·
                refine ⟨14009425821246473930083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1195471003413032442033749 14009425821246473930083)
                ·
                  rfl

theorem cell21_184162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_184162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_184162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_184162 prefixEnd_184162 := by exact prefixLift 184162
  have htrace : WordTrace (prefixWord ++ tailWord_184162) baseStart_184162 baseEnd_184162 := by
    simpa [prefixWord, tailWord_184162, baseEnd_184162] using wordTrace_append hprefix tailTrace_184162
  have hstable : (prefixWord ++ tailWord_184162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184162).length < 2 ^ (prefixWord ++ tailWord_184162).sum := by decide
  have hdescent : baseEnd_184162 < baseStart_184162 := by decide
  rcases family_descends (prefixWord ++ tailWord_184162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184244 : List Nat := [2, 5, 2, 1, 2, 1, 2, 3, 3]
def baseStart_184244 : Nat := 118140960795 + 184244 * 2 ^ 59
def prefixEnd_184244 : Nat := 4983230072969 + 3 ^ 40 * 184244 * 2
def baseEnd_184244 : Nat := 42046990980925501423415

theorem tailTrace_184244 : CollatzResearch.WordTrace tailWord_184244 prefixEnd_184244 42046990980925501423415 := by
  unfold tailWord_184244
  simp only [CollatzResearch.WordTrace]
  refine ⟨3359965372261464607571893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4479953829681952810095857 3359965372261464607571893)
  ·
    refine ⟨314996753649512306959865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3359965372261464607571893 314996753649512306959865)
    ·
      refine ⟨236247565237134230219899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314996753649512306959865 236247565237134230219899)
      ·
        refine ⟨354371347855701345329849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236247565237134230219899 354371347855701345329849)
        ·
          refine ⟨265778510891776008997387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354371347855701345329849 265778510891776008997387)
          ·
            refine ⟨398667766337664013496081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265778510891776008997387 398667766337664013496081)
            ·
              refine ⟨299000824753248010122061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 398667766337664013496081 299000824753248010122061)
              ·
                refine ⟨112125309282468003795773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 299000824753248010122061 112125309282468003795773)
                ·
                  refine ⟨42046990980925501423415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112125309282468003795773 42046990980925501423415)
                  ·
                    rfl

theorem cell21_184244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_184244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_184244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_184244 prefixEnd_184244 := by exact prefixLift 184244
  have htrace : WordTrace (prefixWord ++ tailWord_184244) baseStart_184244 baseEnd_184244 := by
    simpa [prefixWord, tailWord_184244, baseEnd_184244] using wordTrace_append hprefix tailTrace_184244
  have hstable : (prefixWord ++ tailWord_184244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184244).length < 2 ^ (prefixWord ++ tailWord_184244).sum := by decide
  have hdescent : baseEnd_184244 < baseStart_184244 := by decide
  rcases family_descends (prefixWord ++ tailWord_184244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184376 : List Nat := [2, 1, 2, 1, 6, 1, 2, 2, 4]
def baseStart_184376 : Nat := 118140960795 + 184376 * 2 ^ 59
def prefixEnd_184376 : Nat := 4983230072969 + 3 ^ 40 * 184376 * 2
def baseEnd_184376 : Nat := 42077115179322605223145

theorem tailTrace_184376 : CollatzResearch.WordTrace tailWord_184376 prefixEnd_184376 42077115179322605223145 := by
  unfold tailWord_184376
  simp only [CollatzResearch.WordTrace]
  refine ⟨3362372590022357879474491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4483163453363143839299321 3362372590022357879474491)
  ·
    refine ⟨5043558885033536819211737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3362372590022357879474491 5043558885033536819211737)
    ·
      refine ⟨3782669163775152614408803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5043558885033536819211737 3782669163775152614408803)
      ·
        refine ⟨5674003745662728921613205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3782669163775152614408803 5674003745662728921613205)
        ·
          refine ⟨265968925577940418200619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5674003745662728921613205 265968925577940418200619)
          ·
            refine ⟨398953388366910627300929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265968925577940418200619 398953388366910627300929)
            ·
              refine ⟨299215041275182970475697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 398953388366910627300929 299215041275182970475697)
              ·
                refine ⟨224411280956387227856773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299215041275182970475697 224411280956387227856773)
                ·
                  refine ⟨42077115179322605223145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 224411280956387227856773 42077115179322605223145)
                  ·
                    rfl

theorem cell21_184376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 4].length) (baseStart_184376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_184376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_184376 prefixEnd_184376 := by exact prefixLift 184376
  have htrace : WordTrace (prefixWord ++ tailWord_184376) baseStart_184376 baseEnd_184376 := by
    simpa [prefixWord, tailWord_184376, baseEnd_184376] using wordTrace_append hprefix tailTrace_184376
  have hstable : (prefixWord ++ tailWord_184376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184376).length < 2 ^ (prefixWord ++ tailWord_184376).sum := by decide
  have hdescent : baseEnd_184376 < baseStart_184376 := by decide
  rcases family_descends (prefixWord ++ tailWord_184376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184421 : List Nat := [1, 3, 1, 3, 2, 2, 1, 5, 3]
def baseStart_184421 : Nat := 118140960795 + 184421 * 2 ^ 59
def prefixEnd_184421 : Nat := 4983230072969 + 3 ^ 40 * 184421 * 2
def baseEnd_184421 : Nat := 42087384792412526973053

theorem tailTrace_184421 : CollatzResearch.WordTrace tailWord_184421 prefixEnd_184421 42087384792412526973053 := by
  unfold tailWord_184421
  simp only [CollatzResearch.WordTrace]
  refine ⟨6726386464881688444337117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4484257643254458962891411 6726386464881688444337117)
  ·
    refine ⟨2522394924330633166626419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6726386464881688444337117 2522394924330633166626419)
    ·
      refine ⟨3783592386495949749939629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2522394924330633166626419 3783592386495949749939629)
      ·
        refine ⟨1418847144935981156227361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3783592386495949749939629 1418847144935981156227361)
        ·
          refine ⟨1064135358701985867170521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1418847144935981156227361 1064135358701985867170521)
          ·
            refine ⟨798101519026489400377891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1064135358701985867170521 798101519026489400377891)
            ·
              refine ⟨1197152278539734100566837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 798101519026489400377891 1197152278539734100566837)
              ·
                refine ⟨112233026113100071928141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1197152278539734100566837 112233026113100071928141)
                ·
                  refine ⟨42087384792412526973053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112233026113100071928141 42087384792412526973053)
                  ·
                    rfl

theorem cell21_184421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5, 3].length) (baseStart_184421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_184421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_184421 prefixEnd_184421 := by exact prefixLift 184421
  have htrace : WordTrace (prefixWord ++ tailWord_184421) baseStart_184421 baseEnd_184421 := by
    simpa [prefixWord, tailWord_184421, baseEnd_184421] using wordTrace_append hprefix tailTrace_184421
  have hstable : (prefixWord ++ tailWord_184421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184421).length < 2 ^ (prefixWord ++ tailWord_184421).sum := by decide
  have hdescent : baseEnd_184421 < baseStart_184421 := by decide
  rcases family_descends (prefixWord ++ tailWord_184421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184438 : List Nat := [5, 1, 1, 2, 1, 2, 2, 4, 3]
def baseStart_184438 : Nat := 118140960795 + 184438 * 2 ^ 59
def prefixEnd_184438 : Nat := 4983230072969 + 3 ^ 40 * 184438 * 2
def baseEnd_184438 : Nat := 42091264424024275189685

theorem tailTrace_184438 : CollatzResearch.WordTrace tailWord_184438 prefixEnd_184438 42091264424024275189685 := by
  unfold tailWord_184438
  simp only [CollatzResearch.WordTrace]
  refine ⟨420437906613756271731623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4484671003880066898470645 420437906613756271731623)
  ·
    refine ⟨630656859920634407597435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 420437906613756271731623 630656859920634407597435)
    ·
      refine ⟨945985289880951611396153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 630656859920634407597435 945985289880951611396153)
      ·
        refine ⟨709488967410713708547115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 945985289880951611396153 709488967410713708547115)
        ·
          refine ⟨1064233451116070562820673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709488967410713708547115 1064233451116070562820673)
          ·
            refine ⟨798175088337052922115505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1064233451116070562820673 798175088337052922115505)
            ·
              refine ⟨598631316252789691586629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 798175088337052922115505 598631316252789691586629)
              ·
                refine ⟨112243371797398067172493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 598631316252789691586629 112243371797398067172493)
                ·
                  refine ⟨42091264424024275189685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112243371797398067172493 42091264424024275189685)
                  ·
                    rfl

theorem cell21_184438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_184438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_184438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_184438 prefixEnd_184438 := by exact prefixLift 184438
  have htrace : WordTrace (prefixWord ++ tailWord_184438) baseStart_184438 baseEnd_184438 := by
    simpa [prefixWord, tailWord_184438, baseEnd_184438] using wordTrace_append hprefix tailTrace_184438
  have hstable : (prefixWord ++ tailWord_184438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184438).length < 2 ^ (prefixWord ++ tailWord_184438).sum := by decide
  have hdescent : baseEnd_184438 < baseStart_184438 := by decide
  rcases family_descends (prefixWord ++ tailWord_184438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184452 : List Nat := [2, 3, 2, 1, 2, 1, 5, 1, 4]
def baseStart_184452 : Nat := 118140960795 + 184452 * 2 ^ 59
def prefixEnd_184452 : Nat := 4983230072969 + 3 ^ 40 * 184452 * 2
def baseEnd_184452 : Nat := 42094459414763361956323

theorem tailTrace_184452 : CollatzResearch.WordTrace tailWord_184452 prefixEnd_184452 42094459414763361956323 := by
  unfold tailWord_184452
  simp only [CollatzResearch.WordTrace]
  refine ⟨3363758563884690369357805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4485011418512920492477073 3363758563884690369357805)
  ·
    refine ⟨1261409461456758888509177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3363758563884690369357805 1261409461456758888509177)
    ·
      refine ⟨946057096092569166381883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1261409461456758888509177 946057096092569166381883)
      ·
        refine ⟨1419085644138853749572825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 946057096092569166381883 1419085644138853749572825)
        ·
          refine ⟨1064314233104140312179619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1419085644138853749572825 1064314233104140312179619)
          ·
            refine ⟨1596471349656210468269429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1064314233104140312179619 1596471349656210468269429)
            ·
              refine ⟨149669189030269731400259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1596471349656210468269429 149669189030269731400259)
              ·
                refine ⟨224503783545404597100389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149669189030269731400259 224503783545404597100389)
                ·
                  refine ⟨42094459414763361956323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 224503783545404597100389 42094459414763361956323)
                  ·
                    rfl

theorem cell21_184452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_184452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_184452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_184452 prefixEnd_184452 := by exact prefixLift 184452
  have htrace : WordTrace (prefixWord ++ tailWord_184452) baseStart_184452 baseEnd_184452 := by
    simpa [prefixWord, tailWord_184452, baseEnd_184452] using wordTrace_append hprefix tailTrace_184452
  have hstable : (prefixWord ++ tailWord_184452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184452).length < 2 ^ (prefixWord ++ tailWord_184452).sum := by decide
  have hdescent : baseEnd_184452 < baseStart_184452 := by decide
  rcases family_descends (prefixWord ++ tailWord_184452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184677 : List Nat := [1, 3, 1, 3, 1, 4, 2, 6]
def baseStart_184677 : Nat := 118140960795 + 184677 * 2 ^ 59
def prefixEnd_184677 : Nat := 4983230072969 + 3 ^ 40 * 184677 * 2
def baseEnd_184677 : Nat := 14048602493404323568621

theorem tailTrace_184677 : CollatzResearch.WordTrace tailWord_184677 prefixEnd_184677 14048602493404323568621 := by
  unfold tailWord_184677
  simp only [CollatzResearch.WordTrace]
  refine ⟨6735723551954244165656285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4490482367969496110437523 6735723551954244165656285)
  ·
    refine ⟨2525896331982841562121107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6735723551954244165656285 2525896331982841562121107)
    ·
      refine ⟨3788844497974262343181661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2525896331982841562121107 3788844497974262343181661)
      ·
        refine ⟨1420816686740348378693123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3788844497974262343181661 1420816686740348378693123)
        ·
          refine ⟨2131225030110522568039685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1420816686740348378693123 2131225030110522568039685)
          ·
            refine ⟨399604693145722981507441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2131225030110522568039685 399604693145722981507441)
            ·
              refine ⟨299703519859292236130581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 399604693145722981507441 299703519859292236130581)
              ·
                refine ⟨14048602493404323568621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 299703519859292236130581 14048602493404323568621)
                ·
                  rfl

theorem cell21_184677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 6].length) (baseStart_184677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_184677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_184677 prefixEnd_184677 := by exact prefixLift 184677
  have htrace : WordTrace (prefixWord ++ tailWord_184677) baseStart_184677 baseEnd_184677 := by
    simpa [prefixWord, tailWord_184677, baseEnd_184677] using wordTrace_append hprefix tailTrace_184677
  have hstable : (prefixWord ++ tailWord_184677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184677).length < 2 ^ (prefixWord ++ tailWord_184677).sum := by decide
  have hdescent : baseEnd_184677 < baseStart_184677 := by decide
  rcases family_descends (prefixWord ++ tailWord_184677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184680 : List Nat := [2, 1, 4, 2, 2, 1, 4, 1, 4]
def baseStart_184680 : Nat := 118140960795 + 184680 * 2 ^ 59
def prefixEnd_184680 : Nat := 4983230072969 + 3 ^ 40 * 184680 * 2
def baseEnd_184680 : Nat := 42146492121085632155857

theorem tailTrace_184680 : CollatzResearch.WordTrace tailWord_184680 prefixEnd_184680 42146492121085632155857 := by
  unfold tailWord_184680
  simp only [CollatzResearch.WordTrace]
  refine ⟨3367916485471687839007747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4490555313962250452010329 3367916485471687839007747)
  ·
    refine ⟨5051874728207531758511621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3367916485471687839007747 5051874728207531758511621)
    ·
      refine ⟨947226511538912204720929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5051874728207531758511621 947226511538912204720929)
      ·
        refine ⟨710419883654184153540697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 947226511538912204720929 710419883654184153540697)
        ·
          refine ⟨532814912740638115155523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 710419883654184153540697 532814912740638115155523)
          ·
            refine ⟨799222369110957172733285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532814912740638115155523 799222369110957172733285)
            ·
              refine ⟨149854194208304469887491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 799222369110957172733285 149854194208304469887491)
              ·
                refine ⟨224781291312456704831237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149854194208304469887491 224781291312456704831237)
                ·
                  refine ⟨42146492121085632155857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 224781291312456704831237 42146492121085632155857)
                  ·
                    rfl

theorem cell21_184680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 4].length) (baseStart_184680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_184680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_184680 prefixEnd_184680 := by exact prefixLift 184680
  have htrace : WordTrace (prefixWord ++ tailWord_184680) baseStart_184680 baseEnd_184680 := by
    simpa [prefixWord, tailWord_184680, baseEnd_184680] using wordTrace_append hprefix tailTrace_184680
  have hstable : (prefixWord ++ tailWord_184680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184680).length < 2 ^ (prefixWord ++ tailWord_184680).sum := by decide
  have hdescent : baseEnd_184680 < baseStart_184680 := by decide
  rcases family_descends (prefixWord ++ tailWord_184680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184812 : List Nat := [2, 2, 1, 1, 2, 1, 5, 7]
def baseStart_184812 : Nat := 118140960795 + 184812 * 2 ^ 59
def prefixEnd_184812 : Nat := 4983230072969 + 3 ^ 40 * 184812 * 2
def baseEnd_184812 : Nat := 14058872106494245318529

theorem tailTrace_184812 : CollatzResearch.WordTrace tailWord_184812 prefixEnd_184812 14058872106494245318529 := by
  unfold tailWord_184812
  simp only [CollatzResearch.WordTrace]
  refine ⟨3370323703232581110910345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4493764937643441481213793 3370323703232581110910345)
  ·
    refine ⟨2527742777424435833182759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3370323703232581110910345 2527742777424435833182759)
    ·
      refine ⟨3791614166136653749774139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2527742777424435833182759 3791614166136653749774139)
      ·
        refine ⟨5687421249204980624661209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3791614166136653749774139 5687421249204980624661209)
        ·
          refine ⟨4265565936903735468495907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5687421249204980624661209 4265565936903735468495907)
          ·
            refine ⟨6398348905355603202743861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4265565936903735468495907 6398348905355603202743861)
            ·
              refine ⟨599845209877087800257237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6398348905355603202743861 599845209877087800257237)
              ·
                refine ⟨14058872106494245318529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 599845209877087800257237 14058872106494245318529)
                ·
                  rfl

theorem cell21_184812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 7].length) (baseStart_184812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_184812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_184812 prefixEnd_184812 := by exact prefixLift 184812
  have htrace : WordTrace (prefixWord ++ tailWord_184812) baseStart_184812 baseEnd_184812 := by
    simpa [prefixWord, tailWord_184812, baseEnd_184812] using wordTrace_append hprefix tailTrace_184812
  have hstable : (prefixWord ++ tailWord_184812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184812).length < 2 ^ (prefixWord ++ tailWord_184812).sum := by decide
  have hdescent : baseEnd_184812 < baseStart_184812 := by decide
  rcases family_descends (prefixWord ++ tailWord_184812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184919 : List Nat := [1, 1, 3, 2, 2, 2, 3, 2, 5]
def baseStart_184919 : Nat := 118140960795 + 184919 * 2 ^ 59
def prefixEnd_184919 : Nat := 4983230072969 + 3 ^ 40 * 184919 * 2
def baseEnd_184919 : Nat := 42201035177274327672035

theorem tailTrace_184919 : CollatzResearch.WordTrace tailWord_184919 prefixEnd_184919 42201035177274327672035 := by
  unfold tailWord_184919
  simp only [CollatzResearch.WordTrace]
  refine ⟨6744550017077519495965811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4496366678051679663977207 6744550017077519495965811)
  ·
    refine ⟨10116825025616279243948717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6744550017077519495965811 10116825025616279243948717)
    ·
      refine ⟨3793809384606104716480769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10116825025616279243948717 3793809384606104716480769)
      ·
        refine ⟨2845357038454578537360577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3793809384606104716480769 2845357038454578537360577)
        ·
          refine ⟨2134017778840933903020433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2845357038454578537360577 2134017778840933903020433)
          ·
            refine ⟨1600513334130700427265325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2134017778840933903020433 1600513334130700427265325)
            ·
              refine ⟨600192500299012660224497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1600513334130700427265325 600192500299012660224497)
              ·
                refine ⟨450144375224259495168373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 600192500299012660224497 450144375224259495168373)
                ·
                  refine ⟨42201035177274327672035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 450144375224259495168373 42201035177274327672035)
                  ·
                    rfl

theorem cell21_184919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 5].length) (baseStart_184919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_184919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_184919 prefixEnd_184919 := by exact prefixLift 184919
  have htrace : WordTrace (prefixWord ++ tailWord_184919) baseStart_184919 baseEnd_184919 := by
    simpa [prefixWord, tailWord_184919, baseEnd_184919] using wordTrace_append hprefix tailTrace_184919
  have hstable : (prefixWord ++ tailWord_184919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184919).length < 2 ^ (prefixWord ++ tailWord_184919).sum := by decide
  have hdescent : baseEnd_184919 < baseStart_184919 := by decide
  rcases family_descends (prefixWord ++ tailWord_184919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184967 : List Nat := [1, 1, 4, 2, 1, 2, 5, 1, 4]
def baseStart_184967 : Nat := 118140960795 + 184967 * 2 ^ 59
def prefixEnd_184967 : Nat := 4983230072969 + 3 ^ 40 * 184967 * 2
def baseEnd_184967 : Nat := 42211989431236910871937

theorem tailTrace_184967 : CollatzResearch.WordTrace tailWord_184967 prefixEnd_184967 42211989431236910871937 := by
  unfold tailWord_184967
  simp only [CollatzResearch.WordTrace]
  refine ⟨6746300720903623693713155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4497533813935749129142103 6746300720903623693713155)
  ·
    refine ⟨10119451081355435540569733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6746300720903623693713155 10119451081355435540569733)
    ·
      refine ⟨1897397077754144163856825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10119451081355435540569733 1897397077754144163856825)
      ·
        refine ⟨1423047808315608122892619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1897397077754144163856825 1423047808315608122892619)
        ·
          refine ⟨2134571712473412184338929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1423047808315608122892619 2134571712473412184338929)
          ·
            refine ⟨1600928784355059138254197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2134571712473412184338929 1600928784355059138254197)
            ·
              refine ⟨150087073533286794211331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1600928784355059138254197 150087073533286794211331)
              ·
                refine ⟨225130610299930191316997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150087073533286794211331 225130610299930191316997)
                ·
                  refine ⟨42211989431236910871937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 225130610299930191316997 42211989431236910871937)
                  ·
                    rfl

theorem cell21_184967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 4].length) (baseStart_184967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_184967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_184967 prefixEnd_184967 := by exact prefixLift 184967
  have htrace : WordTrace (prefixWord ++ tailWord_184967) baseStart_184967 baseEnd_184967 := by
    simpa [prefixWord, tailWord_184967, baseEnd_184967] using wordTrace_append hprefix tailTrace_184967
  have hstable : (prefixWord ++ tailWord_184967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184967).length < 2 ^ (prefixWord ++ tailWord_184967).sum := by decide
  have hdescent : baseEnd_184967 < baseStart_184967 := by decide
  rcases family_descends (prefixWord ++ tailWord_184967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185116 : List Nat := [2, 2, 3, 1, 1, 4, 8]
def baseStart_185116 : Nat := 118140960795 + 185116 * 2 ^ 59
def prefixEnd_185116 : Nat := 4983230072969 + 3 ^ 40 * 185116 * 2
def baseEnd_185116 : Nat := 4693999251249529209811

theorem tailTrace_185116 : CollatzResearch.WordTrace tailWord_185116 prefixEnd_185116 4693999251249529209811 := by
  unfold tailWord_185116
  simp only [CollatzResearch.WordTrace]
  refine ⟨3375867598681911070443601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4501156798242548093924801 3375867598681911070443601)
  ·
    refine ⟨2531900699011433302832701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3375867598681911070443601 2531900699011433302832701)
    ·
      refine ⟨949462762129287488562263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2531900699011433302832701 949462762129287488562263)
      ·
        refine ⟨1424194143193931232843395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 949462762129287488562263 1424194143193931232843395)
        ·
          refine ⟨2136291214790896849265093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1424194143193931232843395 2136291214790896849265093)
          ·
            refine ⟨400554602773293159237205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2136291214790896849265093 400554602773293159237205)
            ·
              refine ⟨4693999251249529209811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 400554602773293159237205 4693999251249529209811)
              ·
                rfl

theorem cell21_185116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 8].length) (baseStart_185116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_185116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_185116 prefixEnd_185116 := by exact prefixLift 185116
  have htrace : WordTrace (prefixWord ++ tailWord_185116) baseStart_185116 baseEnd_185116 := by
    simpa [prefixWord, tailWord_185116, baseEnd_185116] using wordTrace_append hprefix tailTrace_185116
  have hstable : (prefixWord ++ tailWord_185116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185116).length < 2 ^ (prefixWord ++ tailWord_185116).sum := by decide
  have hdescent : baseEnd_185116 < baseStart_185116 := by decide
  rcases family_descends (prefixWord ++ tailWord_185116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185119 : List Nat := [1, 1, 2, 4, 2, 4, 1, 2, 4]
def baseStart_185119 : Nat := 118140960795 + 185119 * 2 ^ 59
def prefixEnd_185119 : Nat := 4983230072969 + 3 ^ 40 * 185119 * 2
def baseEnd_185119 : Nat := 42246677902118424338293

theorem tailTrace_185119 : CollatzResearch.WordTrace tailWord_185119 prefixEnd_185119 42246677902118424338293 := by
  unfold tailWord_185119
  simp only [CollatzResearch.WordTrace]
  refine ⟨6751844616352953653246411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4501229744235302435497607 6751844616352953653246411)
  ·
    refine ⟨10127766924529430479869617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6751844616352953653246411 10127766924529430479869617)
    ·
      refine ⟨7595825193397072859902213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10127766924529430479869617 7595825193397072859902213)
      ·
        refine ⟨1424217223761951161231665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7595825193397072859902213 1424217223761951161231665)
        ·
          refine ⟨1068162917821463370923749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1424217223761951161231665 1068162917821463370923749)
          ·
            refine ⟨200280547091524382048203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1068162917821463370923749 200280547091524382048203)
            ·
              refine ⟨300420820637286573072305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200280547091524382048203 300420820637286573072305)
              ·
                refine ⟨225315615477964929804229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 300420820637286573072305 225315615477964929804229)
                ·
                  refine ⟨42246677902118424338293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 225315615477964929804229 42246677902118424338293)
                  ·
                    rfl

theorem cell21_185119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 4].length) (baseStart_185119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_185119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_185119 prefixEnd_185119 := by exact prefixLift 185119
  have htrace : WordTrace (prefixWord ++ tailWord_185119) baseStart_185119 baseEnd_185119 := by
    simpa [prefixWord, tailWord_185119, baseEnd_185119] using wordTrace_append hprefix tailTrace_185119
  have hstable : (prefixWord ++ tailWord_185119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185119).length < 2 ^ (prefixWord ++ tailWord_185119).sum := by decide
  have hdescent : baseEnd_185119 < baseStart_185119 := by decide
  rcases family_descends (prefixWord ++ tailWord_185119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185156 : List Nat := [2, 3, 4, 2, 2, 1, 1, 3, 3]
def baseStart_185156 : Nat := 118140960795 + 185156 * 2 ^ 59
def prefixEnd_185156 : Nat := 4983230072969 + 3 ^ 40 * 185156 * 2
def baseEnd_185156 : Nat := 42255121806214582221551

theorem tailTrace_185156 : CollatzResearch.WordTrace tailWord_185156 prefixEnd_185156 42255121806214582221551 := by
  unfold tailWord_185156
  simp only [CollatzResearch.WordTrace]
  refine ⟨3376597058609454486171661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4502129411479272648228881 3376597058609454486171661)
  ·
    refine ⟨1266223896978545432314373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3376597058609454486171661 1266223896978545432314373)
    ·
      refine ⟨237416980683477268558945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1266223896978545432314373 237416980683477268558945)
      ·
        refine ⟨178062735512607951419209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237416980683477268558945 178062735512607951419209)
        ·
          refine ⟨133547051634455963564407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178062735512607951419209 133547051634455963564407)
          ·
            refine ⟨200320577451683945346611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133547051634455963564407 200320577451683945346611)
            ·
              refine ⟨300480866177525918019917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200320577451683945346611 300480866177525918019917)
              ·
                refine ⟨112680324816572219257469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 300480866177525918019917 112680324816572219257469)
                ·
                  refine ⟨42255121806214582221551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112680324816572219257469 42255121806214582221551)
                  ·
                    rfl

theorem cell21_185156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_185156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_185156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_185156 prefixEnd_185156 := by exact prefixLift 185156
  have htrace : WordTrace (prefixWord ++ tailWord_185156) baseStart_185156 baseEnd_185156 := by
    simpa [prefixWord, tailWord_185156, baseEnd_185156] using wordTrace_append hprefix tailTrace_185156
  have hstable : (prefixWord ++ tailWord_185156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185156).length < 2 ^ (prefixWord ++ tailWord_185156).sum := by decide
  have hdescent : baseEnd_185156 < baseStart_185156 := by decide
  rcases family_descends (prefixWord ++ tailWord_185156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185161 : List Nat := [1, 2, 1, 1, 2, 5, 1, 2, 6]
def baseStart_185161 : Nat := 118140960795 + 185161 * 2 ^ 59
def prefixEnd_185161 : Nat := 4983230072969 + 3 ^ 40 * 185161 * 2
def baseEnd_185161 : Nat := 42256262874335684638207

theorem tailTrace_185161 : CollatzResearch.WordTrace tailWord_185161 prefixEnd_185161 42256262874335684638207 := by
  unfold tailWord_185161
  simp only [CollatzResearch.WordTrace]
  refine ⟨6753376482200794826275337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4502250988133863217516891 6753376482200794826275337)
  ·
    refine ⟨5065032361650596119706503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6753376482200794826275337 5065032361650596119706503)
    ·
      refine ⟨7597548542475894179559755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5065032361650596119706503 7597548542475894179559755)
      ·
        refine ⟨11396322813713841269339633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7597548542475894179559755 11396322813713841269339633)
        ·
          refine ⟨8547242110285380952004725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11396322813713841269339633 8547242110285380952004725)
          ·
            refine ⟨801303947839254464250443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8547242110285380952004725 801303947839254464250443)
            ·
              refine ⟨1201955921758881696375665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 801303947839254464250443 1201955921758881696375665)
              ·
                refine ⟨901466941319161272281749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1201955921758881696375665 901466941319161272281749)
                ·
                  refine ⟨42256262874335684638207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 901466941319161272281749 42256262874335684638207)
                  ·
                    rfl

theorem cell21_185161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 6].length) (baseStart_185161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_185161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_185161 prefixEnd_185161 := by exact prefixLift 185161
  have htrace : WordTrace (prefixWord ++ tailWord_185161) baseStart_185161 baseEnd_185161 := by
    simpa [prefixWord, tailWord_185161, baseEnd_185161] using wordTrace_append hprefix tailTrace_185161
  have hstable : (prefixWord ++ tailWord_185161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185161).length < 2 ^ (prefixWord ++ tailWord_185161).sum := by decide
  have hdescent : baseEnd_185161 < baseStart_185161 := by decide
  rcases family_descends (prefixWord ++ tailWord_185161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185192 : List Nat := [2, 1, 4, 2, 1, 2, 1, 8]
def baseStart_185192 : Nat := 118140960795 + 185192 * 2 ^ 59
def prefixEnd_185192 : Nat := 4983230072969 + 3 ^ 40 * 185192 * 2
def baseEnd_185192 : Nat := 14087779165562173207159

theorem tailTrace_185192 : CollatzResearch.WordTrace tailWord_185192 prefixEnd_185192 14087779165562173207159 := by
  unfold tailWord_185192
  simp only [CollatzResearch.WordTrace]
  refine ⟨3377253572544243560326915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4503004763392324747102553 3377253572544243560326915)
  ·
    refine ⟨5065880358816365340490373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3377253572544243560326915 5065880358816365340490373)
    ·
      refine ⟨949852567278068501341945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5065880358816365340490373 949852567278068501341945)
      ·
        refine ⟨712389425458551376006459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 949852567278068501341945 712389425458551376006459)
        ·
          refine ⟨1068584138187827064009689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 712389425458551376006459 1068584138187827064009689)
          ·
            refine ⟨801438103640870298007267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1068584138187827064009689 801438103640870298007267)
            ·
              refine ⟨1202157155461305447010901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 801438103640870298007267 1202157155461305447010901)
              ·
                refine ⟨14087779165562173207159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1202157155461305447010901 14087779165562173207159)
                ·
                  rfl

theorem cell21_185192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 8].length) (baseStart_185192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_185192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_185192 prefixEnd_185192 := by exact prefixLift 185192
  have htrace : WordTrace (prefixWord ++ tailWord_185192) baseStart_185192 baseEnd_185192 := by
    simpa [prefixWord, tailWord_185192, baseEnd_185192] using wordTrace_append hprefix tailTrace_185192
  have hstable : (prefixWord ++ tailWord_185192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185192).length < 2 ^ (prefixWord ++ tailWord_185192).sum := by decide
  have hdescent : baseEnd_185192 < baseStart_185192 := by decide
  rcases family_descends (prefixWord ++ tailWord_185192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185288 : List Nat := [2, 1, 3, 1, 6, 1, 1, 2, 4]
def baseStart_185288 : Nat := 118140960795 + 185288 * 2 ^ 59
def prefixEnd_185288 : Nat := 4983230072969 + 3 ^ 40 * 185288 * 2
def baseEnd_185288 : Nat := 42285246004611686021281

theorem tailTrace_185288 : CollatzResearch.WordTrace tailWord_185288 prefixEnd_185288 42285246004611686021281 := by
  unfold tailWord_185288
  simp only [CollatzResearch.WordTrace]
  refine ⟨3379004276370347758074259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4505339035160463677432345 3379004276370347758074259)
  ·
    refine ⟨5068506414555521637111389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3379004276370347758074259 5068506414555521637111389)
    ·
      refine ⟨1900689905458320613916771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5068506414555521637111389 1900689905458320613916771)
      ·
        refine ⟨2851034858187480920875157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1900689905458320613916771 2851034858187480920875157)
        ·
          refine ⟨133642258977538168166023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2851034858187480920875157 133642258977538168166023)
          ·
            refine ⟨200463388466307252249035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133642258977538168166023 200463388466307252249035)
            ·
              refine ⟨300695082699460878373553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200463388466307252249035 300695082699460878373553)
              ·
                refine ⟨225521312024595658780165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 300695082699460878373553 225521312024595658780165)
                ·
                  refine ⟨42285246004611686021281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 225521312024595658780165 42285246004611686021281)
                  ·
                    rfl

theorem cell21_185288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 4].length) (baseStart_185288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_185288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_185288 prefixEnd_185288 := by exact prefixLift 185288
  have htrace : WordTrace (prefixWord ++ tailWord_185288) baseStart_185288 baseEnd_185288 := by
    simpa [prefixWord, tailWord_185288, baseEnd_185288] using wordTrace_append hprefix tailTrace_185288
  have hstable : (prefixWord ++ tailWord_185288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185288).length < 2 ^ (prefixWord ++ tailWord_185288).sum := by decide
  have hdescent : baseEnd_185288 < baseStart_185288 := by decide
  rcases family_descends (prefixWord ++ tailWord_185288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185409 : List Nat := [1, 2, 5, 1, 3, 1, 1, 4, 3]
def baseStart_185409 : Nat := 118140960795 + 185409 * 2 ^ 59
def prefixEnd_185409 : Nat := 4983230072969 + 3 ^ 40 * 185409 * 2
def baseEnd_185409 : Nat := 42312859853142364504367

theorem tailTrace_185409 : CollatzResearch.WordTrace tailWord_185409 prefixEnd_185409 42312859853142364504367 := by
  unfold tailWord_185409
  simp only [CollatzResearch.WordTrace]
  refine ⟨6762421785302333181303281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4508281190201555454202187 6762421785302333181303281)
  ·
    refine ⟨5071816338976749885977461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6762421785302333181303281 5071816338976749885977461)
    ·
      refine ⟨475482781779070301810387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5071816338976749885977461 475482781779070301810387)
      ·
        refine ⟨713224172668605452715581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475482781779070301810387 713224172668605452715581)
        ·
          refine ⟨267459064750727044768343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 713224172668605452715581 267459064750727044768343)
          ·
            refine ⟨401188597126090567152515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267459064750727044768343 401188597126090567152515)
            ·
              refine ⟨601782895689135850728773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401188597126090567152515 601782895689135850728773)
              ·
                refine ⟨112834292941712972011645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 601782895689135850728773 112834292941712972011645)
                ·
                  refine ⟨42312859853142364504367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112834292941712972011645 42312859853142364504367)
                  ·
                    rfl

theorem cell21_185409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4, 3].length) (baseStart_185409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_185409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_185409 prefixEnd_185409 := by exact prefixLift 185409
  have htrace : WordTrace (prefixWord ++ tailWord_185409) baseStart_185409 baseEnd_185409 := by
    simpa [prefixWord, tailWord_185409, baseEnd_185409] using wordTrace_append hprefix tailTrace_185409
  have hstable : (prefixWord ++ tailWord_185409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185409).length < 2 ^ (prefixWord ++ tailWord_185409).sum := by decide
  have hdescent : baseEnd_185409 < baseStart_185409 := by decide
  rcases family_descends (prefixWord ++ tailWord_185409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185479 : List Nat := [1, 1, 4, 2, 1, 1, 1, 10]
def baseStart_185479 : Nat := 118140960795 + 185479 * 2 ^ 59
def prefixEnd_185479 : Nat := 4983230072969 + 3 ^ 40 * 185479 * 2
def baseEnd_185479 : Nat := 14109611602279266112519

theorem tailTrace_185479 : CollatzResearch.WordTrace tailWord_185479 prefixEnd_185479 14109611602279266112519 := by
  unfold tailWord_185479
  simp only [CollatzResearch.WordTrace]
  refine ⟨6764974895048735136351491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4509983263365823424234327 6764974895048735136351491)
  ·
    refine ⟨10147462342573102704527237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6764974895048735136351491 10147462342573102704527237)
    ·
      refine ⟨1902649189232456757098857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10147462342573102704527237 1902649189232456757098857)
      ·
        refine ⟨1426986891924342567824143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1902649189232456757098857 1426986891924342567824143)
        ·
          refine ⟨2140480337886513851736215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1426986891924342567824143 2140480337886513851736215)
          ·
            refine ⟨3210720506829770777604323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2140480337886513851736215 3210720506829770777604323)
            ·
              refine ⟨4816080760244656166406485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3210720506829770777604323 4816080760244656166406485)
              ·
                refine ⟨14109611602279266112519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4816080760244656166406485 14109611602279266112519)
                ·
                  rfl

theorem cell21_185479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 10].length) (baseStart_185479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_185479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_185479 prefixEnd_185479 := by exact prefixLift 185479
  have htrace : WordTrace (prefixWord ++ tailWord_185479) baseStart_185479 baseEnd_185479 := by
    simpa [prefixWord, tailWord_185479, baseEnd_185479] using wordTrace_append hprefix tailTrace_185479
  have hstable : (prefixWord ++ tailWord_185479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185479).length < 2 ^ (prefixWord ++ tailWord_185479).sum := by decide
  have hdescent : baseEnd_185479 < baseStart_185479 := by decide
  rcases family_descends (prefixWord ++ tailWord_185479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185496 : List Nat := [2, 1, 2, 4, 2, 2, 1, 7]
def baseStart_185496 : Nat := 118140960795 + 185496 * 2 ^ 59
def prefixEnd_185496 : Nat := 4983230072969 + 3 ^ 40 * 185496 * 2
def baseEnd_185496 : Nat := 14110904812816515518063

theorem tailTrace_185496 : CollatzResearch.WordTrace tailWord_185496 prefixEnd_185496 14110904812816515518063 := by
  unfold tailWord_185496
  simp only [CollatzResearch.WordTrace]
  refine ⟨3382797467993573519860171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4510396623991431359813561 3382797467993573519860171)
  ·
    refine ⟨5074196201990360279790257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3382797467993573519860171 5074196201990360279790257)
    ·
      refine ⟨3805647151492770209842693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5074196201990360279790257 3805647151492770209842693)
      ·
        refine ⟨713558840904894414345505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3805647151492770209842693 713558840904894414345505)
        ·
          refine ⟨535169130678670810759129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 713558840904894414345505 535169130678670810759129)
          ·
            refine ⟨401376848009003108069347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 535169130678670810759129 401376848009003108069347)
            ·
              refine ⟨602065272013504662104021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401376848009003108069347 602065272013504662104021)
              ·
                refine ⟨14110904812816515518063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 602065272013504662104021 14110904812816515518063)
                ·
                  rfl

theorem cell21_185496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 7].length) (baseStart_185496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_185496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_185496 prefixEnd_185496 := by exact prefixLift 185496
  have htrace : WordTrace (prefixWord ++ tailWord_185496) baseStart_185496 baseEnd_185496 := by
    simpa [prefixWord, tailWord_185496, baseEnd_185496] using wordTrace_append hprefix tailTrace_185496
  have hstable : (prefixWord ++ tailWord_185496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185496).length < 2 ^ (prefixWord ++ tailWord_185496).sum := by decide
  have hdescent : baseEnd_185496 < baseStart_185496 := by decide
  rcases family_descends (prefixWord ++ tailWord_185496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185502 : List Nat := [4, 3, 1, 1, 2, 3, 1, 3, 3]
def baseStart_185502 : Nat := 118140960795 + 185502 * 2 ^ 59
def prefixEnd_185502 : Nat := 4983230072969 + 3 ^ 40 * 185502 * 2
def baseEnd_185502 : Nat := 42334083720194869454177

theorem tailTrace_185502 : CollatzResearch.WordTrace tailWord_185502 prefixEnd_185502 42334083720194869454177 := by
  unfold tailWord_185502
  simp only [CollatzResearch.WordTrace]
  refine ⟨845726721745676258054845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4510542515976940042959173 845726721745676258054845)
  ·
    refine ⟨317147520654628596770567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 845726721745676258054845 317147520654628596770567)
    ·
      refine ⟨475721280981942895155851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317147520654628596770567 475721280981942895155851)
      ·
        refine ⟨713581921472914342733777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475721280981942895155851 713581921472914342733777)
        ·
          refine ⟨535186441104685757050333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 713581921472914342733777 535186441104685757050333)
          ·
            refine ⟨200694915414257158893875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 535186441104685757050333 200694915414257158893875)
            ·
              refine ⟨301042373121385738340813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200694915414257158893875 301042373121385738340813)
              ·
                refine ⟨112890889920519651877805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 301042373121385738340813 112890889920519651877805)
                ·
                  refine ⟨42334083720194869454177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112890889920519651877805 42334083720194869454177)
                  ·
                    rfl

theorem cell21_185502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_185502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_185502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_185502 prefixEnd_185502 := by exact prefixLift 185502
  have htrace : WordTrace (prefixWord ++ tailWord_185502) baseStart_185502 baseEnd_185502 := by
    simpa [prefixWord, tailWord_185502, baseEnd_185502] using wordTrace_append hprefix tailTrace_185502
  have hstable : (prefixWord ++ tailWord_185502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185502).length < 2 ^ (prefixWord ++ tailWord_185502).sum := by decide
  have hdescent : baseEnd_185502 < baseStart_185502 := by decide
  rcases family_descends (prefixWord ++ tailWord_185502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185575 : List Nat := [1, 1, 5, 3, 2, 1, 2, 2, 4]
def baseStart_185575 : Nat := 118140960795 + 185575 * 2 ^ 59
def prefixEnd_185575 : Nat := 4983230072969 + 3 ^ 40 * 185575 * 2
def baseEnd_185575 : Nat := 42350743314762964737361

theorem tailTrace_185575 : CollatzResearch.WordTrace tailWord_185575 prefixEnd_185575 42350743314762964737361 := by
  unfold tailWord_185575
  simp only [CollatzResearch.WordTrace]
  refine ⟨6768476302700943531846179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4512317535133962354564119 6768476302700943531846179)
  ·
    refine ⟨10152714454051415297769269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6768476302700943531846179 10152714454051415297769269)
    ·
      refine ⟨951816980067320184165869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10152714454051415297769269 951816980067320184165869)
      ·
        refine ⟨356931367525245069062201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 951816980067320184165869 356931367525245069062201)
        ·
          refine ⟨267698525643933801796651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356931367525245069062201 267698525643933801796651)
          ·
            refine ⟨401547788465900702694977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267698525643933801796651 401547788465900702694977)
            ·
              refine ⟨301160841349425527021233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 401547788465900702694977 301160841349425527021233)
              ·
                refine ⟨225870631012069145265925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301160841349425527021233 225870631012069145265925)
                ·
                  refine ⟨42350743314762964737361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 225870631012069145265925 42350743314762964737361)
                  ·
                    rfl

theorem cell21_185575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 4].length) (baseStart_185575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_185575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_185575 prefixEnd_185575 := by exact prefixLift 185575
  have htrace : WordTrace (prefixWord ++ tailWord_185575) baseStart_185575 baseEnd_185575 := by
    simpa [prefixWord, tailWord_185575, baseEnd_185575] using wordTrace_append hprefix tailTrace_185575
  have hstable : (prefixWord ++ tailWord_185575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185575).length < 2 ^ (prefixWord ++ tailWord_185575).sum := by decide
  have hdescent : baseEnd_185575 < baseStart_185575 := by decide
  rcases family_descends (prefixWord ++ tailWord_185575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185600 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 8]
def baseStart_185600 : Nat := 118140960795 + 185600 * 2 ^ 59
def prefixEnd_185600 : Nat := 4983230072969 + 3 ^ 40 * 185600 * 2
def baseEnd_185600 : Nat := 42356448655368476820643

theorem tailTrace_185600 : CollatzResearch.WordTrace tailWord_185600 prefixEnd_185600 42356448655368476820643 := by
  unfold tailWord_185600
  simp only [CollatzResearch.WordTrace]
  refine ⟨3384694063805186400753127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4512925418406915201004169 3384694063805186400753127)
  ·
    refine ⟨5077041095707779601129691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3384694063805186400753127 5077041095707779601129691)
    ·
      refine ⟨7615561643561669401694537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5077041095707779601129691 7615561643561669401694537)
      ·
        refine ⟨5711671232671252051270903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7615561643561669401694537 5711671232671252051270903)
        ·
          refine ⟨8567506849006878076906355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5711671232671252051270903 8567506849006878076906355)
          ·
            refine ⟨12851260273510317115359533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8567506849006878076906355 12851260273510317115359533)
            ·
              refine ⟨4819222602566368918259825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12851260273510317115359533 4819222602566368918259825)
              ·
                refine ⟨3614416951924776688694869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4819222602566368918259825 3614416951924776688694869)
                ·
                  refine ⟨42356448655368476820643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3614416951924776688694869 42356448655368476820643)
                  ·
                    rfl

theorem cell21_185600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_185600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_185600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_185600 prefixEnd_185600 := by exact prefixLift 185600
  have htrace : WordTrace (prefixWord ++ tailWord_185600) baseStart_185600 baseEnd_185600 := by
    simpa [prefixWord, tailWord_185600, baseEnd_185600] using wordTrace_append hprefix tailTrace_185600
  have hstable : (prefixWord ++ tailWord_185600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185600).length < 2 ^ (prefixWord ++ tailWord_185600).sum := by decide
  have hdescent : baseEnd_185600 < baseStart_185600 := by decide
  rcases family_descends (prefixWord ++ tailWord_185600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185634 : List Nat := [3, 3, 1, 1, 4, 1, 1, 1, 6]
def baseStart_185634 : Nat := 118140960795 + 185634 * 2 ^ 59
def prefixEnd_185634 : Nat := 4983230072969 + 3 ^ 40 * 185634 * 2
def baseEnd_185634 : Nat := 42364207918591973253907

theorem tailTrace_185634 : CollatzResearch.WordTrace tailWord_185634 prefixEnd_185634 42364207918591973253907 := by
  unfold tailWord_185634
  simp only [CollatzResearch.WordTrace]
  refine ⟨1692657052371799152060989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4513752139658131072162637 1692657052371799152060989)
  ·
    refine ⟨634746394639424682022871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1692657052371799152060989 634746394639424682022871)
    ·
      refine ⟨952119591959137023034307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 634746394639424682022871 952119591959137023034307)
      ·
        refine ⟨1428179387938705534551461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 952119591959137023034307 1428179387938705534551461)
        ·
          refine ⟨267783635238507287728399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1428179387938705534551461 267783635238507287728399)
          ·
            refine ⟨401675452857760931592599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267783635238507287728399 401675452857760931592599)
            ·
              refine ⟨602513179286641397388899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401675452857760931592599 602513179286641397388899)
              ·
                refine ⟨903769768929962096083349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 602513179286641397388899 903769768929962096083349)
                ·
                  refine ⟨42364207918591973253907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 903769768929962096083349 42364207918591973253907)
                  ·
                    rfl

theorem cell21_185634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_185634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_185634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_185634 prefixEnd_185634 := by exact prefixLift 185634
  have htrace : WordTrace (prefixWord ++ tailWord_185634) baseStart_185634 baseEnd_185634 := by
    simpa [prefixWord, tailWord_185634, baseEnd_185634] using wordTrace_append hprefix tailTrace_185634
  have hstable : (prefixWord ++ tailWord_185634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185634).length < 2 ^ (prefixWord ++ tailWord_185634).sum := by decide
  have hdescent : baseEnd_185634 < baseStart_185634 := by decide
  rcases family_descends (prefixWord ++ tailWord_185634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185665 : List Nat := [1, 2, 5, 2, 1, 1, 4, 5]
def baseStart_185665 : Nat := 118140960795 + 185665 * 2 ^ 59
def prefixEnd_185665 : Nat := 4983230072969 + 3 ^ 40 * 185665 * 2
def baseEnd_185665 : Nat := 14123760846980936079059

theorem tailTrace_185665 : CollatzResearch.WordTrace tailWord_185665 prefixEnd_185665 14123760846980936079059 := by
  unfold tailWord_185665
  simp only [CollatzResearch.WordTrace]
  refine ⟨6771758872374888902622449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4514505914916592601748299 6771758872374888902622449)
  ·
    refine ⟨5078819154281166676966837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6771758872374888902622449 5078819154281166676966837)
    ·
      refine ⟨476139295713859375965641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5078819154281166676966837 476139295713859375965641)
      ·
        refine ⟨357104471785394531974231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 476139295713859375965641 357104471785394531974231)
        ·
          refine ⟨535656707678091797961347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357104471785394531974231 535656707678091797961347)
          ·
            refine ⟨803485061517137696942021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535656707678091797961347 803485061517137696942021)
            ·
              refine ⟨150653449034463318176629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 803485061517137696942021 150653449034463318176629)
              ·
                refine ⟨14123760846980936079059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150653449034463318176629 14123760846980936079059)
                ·
                  rfl

theorem cell21_185665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 5].length) (baseStart_185665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_185665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_185665 prefixEnd_185665 := by exact prefixLift 185665
  have htrace : WordTrace (prefixWord ++ tailWord_185665) baseStart_185665 baseEnd_185665 := by
    simpa [prefixWord, tailWord_185665, baseEnd_185665] using wordTrace_append hprefix tailTrace_185665
  have hstable : (prefixWord ++ tailWord_185665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185665).length < 2 ^ (prefixWord ++ tailWord_185665).sum := by decide
  have hdescent : baseEnd_185665 < baseStart_185665 := by decide
  rcases family_descends (prefixWord ++ tailWord_185665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185758 : List Nat := [4, 3, 1, 2, 2, 2, 1, 6]
def baseStart_185758 : Nat := 118140960795 + 185758 * 2 ^ 59
def prefixEnd_185758 : Nat := 4983230072969 + 3 ^ 40 * 185758 * 2
def baseEnd_185758 : Nat := 14130835469331771062329

theorem tailTrace_185758 : CollatzResearch.WordTrace tailWord_185758 prefixEnd_185758 14130835469331771062329 := by
  unfold tailWord_185758
  simp only [CollatzResearch.WordTrace]
  refine ⟨846893857629745723219741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4516767240691977190505285 846893857629745723219741)
  ·
    refine ⟨317585196611154646207403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 846893857629745723219741 317585196611154646207403)
    ·
      refine ⟨476377794916731969311105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317585196611154646207403 476377794916731969311105)
      ·
        refine ⟨357283346187548976983329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 476377794916731969311105 357283346187548976983329)
        ·
          refine ⟨267962509640661732737497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357283346187548976983329 267962509640661732737497)
          ·
            refine ⟨200971882230496299553123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267962509640661732737497 200971882230496299553123)
            ·
              refine ⟨301457823345744449329685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200971882230496299553123 301457823345744449329685)
              ·
                refine ⟨14130835469331771062329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 301457823345744449329685 14130835469331771062329)
                ·
                  rfl

theorem cell21_185758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_185758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_185758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_185758 prefixEnd_185758 := by exact prefixLift 185758
  have htrace : WordTrace (prefixWord ++ tailWord_185758) baseStart_185758 baseEnd_185758 := by
    simpa [prefixWord, tailWord_185758, baseEnd_185758] using wordTrace_append hprefix tailTrace_185758
  have hstable : (prefixWord ++ tailWord_185758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185758).length < 2 ^ (prefixWord ++ tailWord_185758).sum := by decide
  have hdescent : baseEnd_185758 < baseStart_185758 := by decide
  rcases family_descends (prefixWord ++ tailWord_185758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185834 : List Nat := [3, 1, 3, 1, 5, 1, 2, 5]
def baseStart_185834 : Nat := 118140960795 + 185834 * 2 ^ 59
def prefixEnd_185834 : Nat := 4983230072969 + 3 ^ 40 * 185834 * 2
def baseEnd_185834 : Nat := 14136616881145356640055

theorem tailTrace_185834 : CollatzResearch.WordTrace tailWord_185834 prefixEnd_185834 14136616881145356640055 := by
  unfold tailWord_185834
  simp only [CollatzResearch.WordTrace]
  refine ⟨1694480702190657691381139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4518615205841753843683037 1694480702190657691381139)
  ·
    refine ⟨2541721053285986537071709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1694480702190657691381139 2541721053285986537071709)
    ·
      refine ⟨953145394982244951401891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2541721053285986537071709 953145394982244951401891)
      ·
        refine ⟨1429718092473367427102837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 953145394982244951401891 1429718092473367427102837)
        ·
          refine ⟨134036071169378196290891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1429718092473367427102837 134036071169378196290891)
          ·
            refine ⟨201054106754067294436337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134036071169378196290891 201054106754067294436337)
            ·
              refine ⟨150790580065550470827253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201054106754067294436337 150790580065550470827253)
              ·
                refine ⟨14136616881145356640055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150790580065550470827253 14136616881145356640055)
                ·
                  rfl

theorem cell21_185834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 5].length) (baseStart_185834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_185834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_185834 prefixEnd_185834 := by exact prefixLift 185834
  have htrace : WordTrace (prefixWord ++ tailWord_185834) baseStart_185834 baseEnd_185834 := by
    simpa [prefixWord, tailWord_185834, baseEnd_185834] using wordTrace_append hprefix tailTrace_185834
  have hstable : (prefixWord ++ tailWord_185834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185834).length < 2 ^ (prefixWord ++ tailWord_185834).sum := by decide
  have hdescent : baseEnd_185834 < baseStart_185834 := by decide
  rcases family_descends (prefixWord ++ tailWord_185834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185848 : List Nat := [2, 1, 2, 1, 1, 7, 1, 3, 3]
def baseStart_185848 : Nat := 118140960795 + 185848 * 2 ^ 59
def prefixEnd_185848 : Nat := 4983230072969 + 3 ^ 40 * 185848 * 2
def baseEnd_185848 : Nat := 42413045634175156686803

theorem tailTrace_185848 : CollatzResearch.WordTrace tailWord_185848 prefixEnd_185848 42413045634175156686803 := by
  unfold tailWord_185848
  simp only [CollatzResearch.WordTrace]
  refine ⟨3389216715355955578267099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4518955620474607437689465 3389216715355955578267099)
  ·
    refine ⟨5083825073033933367400649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3389216715355955578267099 5083825073033933367400649)
    ·
      refine ⟨3812868804775450025550487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5083825073033933367400649 3812868804775450025550487)
      ·
        refine ⟨5719303207163175038325731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3812868804775450025550487 5719303207163175038325731)
        ·
          refine ⟨8578954810744762557488597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5719303207163175038325731 8578954810744762557488597)
          ·
            refine ⟨201069253376830372441139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 8578954810744762557488597 201069253376830372441139)
            ·
              refine ⟨301603880065245558661709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201069253376830372441139 301603880065245558661709)
              ·
                refine ⟨113101455024467084498141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 301603880065245558661709 113101455024467084498141)
                ·
                  refine ⟨42413045634175156686803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113101455024467084498141 42413045634175156686803)
                  ·
                    rfl

theorem cell21_185848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3, 3].length) (baseStart_185848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_185848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_185848 prefixEnd_185848 := by exact prefixLift 185848
  have htrace : WordTrace (prefixWord ++ tailWord_185848) baseStart_185848 baseEnd_185848 := by
    simpa [prefixWord, tailWord_185848, baseEnd_185848] using wordTrace_append hprefix tailTrace_185848
  have hstable : (prefixWord ++ tailWord_185848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185848).length < 2 ^ (prefixWord ++ tailWord_185848).sum := by decide
  have hdescent : baseEnd_185848 < baseStart_185848 := by decide
  rcases family_descends (prefixWord ++ tailWord_185848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185890 : List Nat := [3, 3, 1, 1, 1, 1, 2, 4, 5]
def baseStart_185890 : Nat := 118140960795 + 185890 * 2 ^ 59
def prefixEnd_185890 : Nat := 4983230072969 + 3 ^ 40 * 185890 * 2
def baseEnd_185890 : Nat := 42422630606392416986717

theorem tailTrace_185890 : CollatzResearch.WordTrace tailWord_185890 prefixEnd_185890 42422630606392416986717 := by
  unfold tailWord_185890
  simp only [CollatzResearch.WordTrace]
  refine ⟨1694991324139938082390781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4519976864373168219708749 1694991324139938082390781)
  ·
    refine ⟨635621746552476780896543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1694991324139938082390781 635621746552476780896543)
    ·
      refine ⟨953432619828715171344815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 635621746552476780896543 953432619828715171344815)
      ·
        refine ⟨1430148929743072757017223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 953432619828715171344815 1430148929743072757017223)
        ·
          refine ⟨2145223394614609135525835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1430148929743072757017223 2145223394614609135525835)
          ·
            refine ⟨3217835091921913703288753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2145223394614609135525835 3217835091921913703288753)
            ·
              refine ⟨2413376318941435277466565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3217835091921913703288753 2413376318941435277466565)
              ·
                refine ⟨452508059801519114524981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2413376318941435277466565 452508059801519114524981)
                ·
                  refine ⟨42422630606392416986717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 452508059801519114524981 42422630606392416986717)
                  ·
                    rfl

theorem cell21_185890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_185890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_185890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_185890 prefixEnd_185890 := by exact prefixLift 185890
  have htrace : WordTrace (prefixWord ++ tailWord_185890) baseStart_185890 baseEnd_185890 := by
    simpa [prefixWord, tailWord_185890, baseEnd_185890] using wordTrace_append hprefix tailTrace_185890
  have hstable : (prefixWord ++ tailWord_185890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185890).length < 2 ^ (prefixWord ++ tailWord_185890).sum := by decide
  have hdescent : baseEnd_185890 < baseStart_185890 := by decide
  rcases family_descends (prefixWord ++ tailWord_185890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186042 : List Nat := [3, 1, 1, 1, 2, 4, 3, 1, 5]
def baseStart_186042 : Nat := 118140960795 + 186042 * 2 ^ 59
def prefixEnd_186042 : Nat := 4983230072969 + 3 ^ 40 * 186042 * 2
def baseEnd_186042 : Nat := 42457319077273930453073

theorem tailTrace_186042 : CollatzResearch.WordTrace tailWord_186042 prefixEnd_186042 42457319077273930453073 := by
  unfold tailWord_186042
  simp only [CollatzResearch.WordTrace]
  refine ⟨1696377298002270572274095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4523672794672721526064253 1696377298002270572274095)
  ·
    refine ⟨2544565947003405858411143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1696377298002270572274095 2544565947003405858411143)
    ·
      refine ⟨3816848920505108787616715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2544565947003405858411143 3816848920505108787616715)
      ·
        refine ⟨5725273380757663181425073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3816848920505108787616715 5725273380757663181425073)
        ·
          refine ⟨4293955035568247386068805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5725273380757663181425073 4293955035568247386068805)
          ·
            refine ⟨805116569169046384887901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4293955035568247386068805 805116569169046384887901)
            ·
              refine ⟨301918713438392394332963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 805116569169046384887901 301918713438392394332963)
              ·
                refine ⟨452878070157588591499445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301918713438392394332963 452878070157588591499445)
                ·
                  refine ⟨42457319077273930453073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 452878070157588591499445 42457319077273930453073)
                  ·
                    rfl

theorem cell21_186042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_186042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_186042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_186042 prefixEnd_186042 := by exact prefixLift 186042
  have htrace : WordTrace (prefixWord ++ tailWord_186042) baseStart_186042 baseEnd_186042 := by
    simpa [prefixWord, tailWord_186042, baseEnd_186042] using wordTrace_append hprefix tailTrace_186042
  have hstable : (prefixWord ++ tailWord_186042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186042).length < 2 ^ (prefixWord ++ tailWord_186042).sum := by decide
  have hdescent : baseEnd_186042 < baseStart_186042 := by decide
  rcases family_descends (prefixWord ++ tailWord_186042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186087 : List Nat := [1, 1, 5, 4, 10]
def baseStart_186087 : Nat := 118140960795 + 186087 * 2 ^ 59
def prefixEnd_186087 : Nat := 4983230072969 + 3 ^ 40 * 186087 * 2
def baseEnd_186087 : Nat := 524291218399553730901

theorem tailTrace_186087 : CollatzResearch.WordTrace tailWord_186087 prefixEnd_186087 524291218399553730901 := by
  unfold tailWord_186087
  simp only [CollatzResearch.WordTrace]
  refine ⟨6787150476846054974484515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4524766984564036649656343 6787150476846054974484515)
  ·
    refine ⟨10180725715269082461726773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6787150476846054974484515 10180725715269082461726773)
    ·
      refine ⟨954443035806476480786885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10180725715269082461726773 954443035806476480786885)
      ·
        refine ⟨178958069213714340147541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 954443035806476480786885 178958069213714340147541)
        ·
          refine ⟨524291218399553730901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 178958069213714340147541 524291218399553730901)
          ·
            rfl

theorem cell21_186087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 10].length) (baseStart_186087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_186087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_186087 prefixEnd_186087 := by exact prefixLift 186087
  have htrace : WordTrace (prefixWord ++ tailWord_186087) baseStart_186087 baseEnd_186087 := by
    simpa [prefixWord, tailWord_186087, baseEnd_186087] using wordTrace_append hprefix tailTrace_186087
  have hstable : (prefixWord ++ tailWord_186087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186087).length < 2 ^ (prefixWord ++ tailWord_186087).sum := by decide
  have hdescent : baseEnd_186087 < baseStart_186087 := by decide
  rcases family_descends (prefixWord ++ tailWord_186087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186093 : List Nat := [1, 5, 1, 2, 1, 4, 2, 2, 3]
def baseStart_186093 : Nat := 118140960795 + 186093 * 2 ^ 59
def prefixEnd_186093 : Nat := 4983230072969 + 3 ^ 40 * 186093 * 2
def baseEnd_186093 : Nat := 42468957972109175102969

theorem tailTrace_186093 : CollatzResearch.WordTrace tailWord_186093 prefixEnd_186093 42468957972109175102969 := by
  unfold tailWord_186093
  simp only [CollatzResearch.WordTrace]
  refine ⟨6787369314824317999202933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4524912876549545332801955 6787369314824317999202933)
  ·
    refine ⟨636315873264779812425275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6787369314824317999202933 636315873264779812425275)
    ·
      refine ⟨954473809897169718637913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 636315873264779812425275 954473809897169718637913)
      ·
        refine ⟨715855357422877288978435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 954473809897169718637913 715855357422877288978435)
        ·
          refine ⟨1073783036134315933467653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 715855357422877288978435 1073783036134315933467653)
          ·
            refine ⟨201334319275184237525185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1073783036134315933467653 201334319275184237525185)
            ·
              refine ⟨151000739456388178143889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201334319275184237525185 151000739456388178143889)
              ·
                refine ⟨113250554592291133607917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151000739456388178143889 113250554592291133607917)
                ·
                  refine ⟨42468957972109175102969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113250554592291133607917 42468957972109175102969)
                  ·
                    rfl

theorem cell21_186093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_186093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_186093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_186093 prefixEnd_186093 := by exact prefixLift 186093
  have htrace : WordTrace (prefixWord ++ tailWord_186093) baseStart_186093 baseEnd_186093 := by
    simpa [prefixWord, tailWord_186093, baseEnd_186093] using wordTrace_append hprefix tailTrace_186093
  have hstable : (prefixWord ++ tailWord_186093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186093).length < 2 ^ (prefixWord ++ tailWord_186093).sum := by decide
  have hdescent : baseEnd_186093 < baseStart_186093 := by decide
  rcases family_descends (prefixWord ++ tailWord_186093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186135 : List Nat := [1, 1, 3, 4, 2, 1, 1, 5, 3]
def baseStart_186135 : Nat := 118140960795 + 186135 * 2 ^ 59
def prefixEnd_186135 : Nat := 4983230072969 + 3 ^ 40 * 186135 * 2
def baseEnd_186135 : Nat := 42478542944326435402883

theorem tailTrace_186135 : CollatzResearch.WordTrace tailWord_186135 prefixEnd_186135 42478542944326435402883 := by
  unfold tailWord_186135
  simp only [CollatzResearch.WordTrace]
  refine ⟨6788901180672159172231859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4525934120448106114821239 6788901180672159172231859)
  ·
    refine ⟨10183351771008238758347789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6788901180672159172231859 10183351771008238758347789)
    ·
      refine ⟨3818756914128089534380421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10183351771008238758347789 3818756914128089534380421)
      ·
        refine ⟨716016921399016787696329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3818756914128089534380421 716016921399016787696329)
        ·
          refine ⟨537012691049262590772247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 716016921399016787696329 537012691049262590772247)
          ·
            refine ⟨805519036573893886158371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537012691049262590772247 805519036573893886158371)
            ·
              refine ⟨1208278554860840829237557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 805519036573893886158371 1208278554860840829237557)
              ·
                refine ⟨113276114518203827741021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1208278554860840829237557 113276114518203827741021)
                ·
                  refine ⟨42478542944326435402883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113276114518203827741021 42478542944326435402883)
                  ·
                    rfl

theorem cell21_186135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5, 3].length) (baseStart_186135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_186135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_186135 prefixEnd_186135 := by exact prefixLift 186135
  have htrace : WordTrace (prefixWord ++ tailWord_186135) baseStart_186135 baseEnd_186135 := by
    simpa [prefixWord, tailWord_186135, baseEnd_186135] using wordTrace_append hprefix tailTrace_186135
  have hstable : (prefixWord ++ tailWord_186135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186135).length < 2 ^ (prefixWord ++ tailWord_186135).sum := by decide
  have hdescent : baseEnd_186135 < baseStart_186135 := by decide
  rcases family_descends (prefixWord ++ tailWord_186135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186149 : List Nat := [1, 3, 1, 2, 3, 2, 3, 2, 4]
def baseStart_186149 : Nat := 118140960795 + 186149 * 2 ^ 59
def prefixEnd_186149 : Nat := 4983230072969 + 3 ^ 40 * 186149 * 2
def baseEnd_186149 : Nat := 42481737935065522169521

theorem tailTrace_186149 : CollatzResearch.WordTrace tailWord_186149 prefixEnd_186149 42481737935065522169521 := by
  unfold tailWord_186149
  simp only [CollatzResearch.WordTrace]
  refine ⟨6789411802621439563241501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4526274535080959708827667 6789411802621439563241501)
  ·
    refine ⟨2546029425983039836215563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6789411802621439563241501 2546029425983039836215563)
    ·
      refine ⟨3819044138974559754323345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2546029425983039836215563 3819044138974559754323345)
      ·
        refine ⟨2864283104230919815742509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3819044138974559754323345 2864283104230919815742509)
        ·
          refine ⟨1074106164086594930903441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2864283104230919815742509 1074106164086594930903441)
          ·
            refine ⟨805579623064946198177581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1074106164086594930903441 805579623064946198177581)
            ·
              refine ⟨302092358649354824316593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 805579623064946198177581 302092358649354824316593)
              ·
                refine ⟨226569268987016118237445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302092358649354824316593 226569268987016118237445)
                ·
                  refine ⟨42481737935065522169521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 226569268987016118237445 42481737935065522169521)
                  ·
                    rfl

theorem cell21_186149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_186149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_186149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_186149 prefixEnd_186149 := by exact prefixLift 186149
  have htrace : WordTrace (prefixWord ++ tailWord_186149) baseStart_186149 baseEnd_186149 := by
    simpa [prefixWord, tailWord_186149, baseEnd_186149] using wordTrace_append hprefix tailTrace_186149
  have hstable : (prefixWord ++ tailWord_186149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186149).length < 2 ^ (prefixWord ++ tailWord_186149).sum := by decide
  have hdescent : baseEnd_186149 < baseStart_186149 := by decide
  rcases family_descends (prefixWord ++ tailWord_186149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186208 : List Nat := [2, 1, 1, 3, 3, 2, 2, 1, 6]
def baseStart_186208 : Nat := 118140960795 + 186208 * 2 ^ 59
def prefixEnd_186208 : Nat := 4983230072969 + 3 ^ 40 * 186208 * 2
def baseEnd_186208 : Nat := 42495202538894530686067

theorem tailTrace_186208 : CollatzResearch.WordTrace tailWord_186208 prefixEnd_186208 42495202538894530686067 := by
  unfold tailWord_186208
  simp only [CollatzResearch.WordTrace]
  refine ⟨3395781854703846319819639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4527709139605128426426185 3395781854703846319819639)
  ·
    refine ⟨5093672782055769479729459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3395781854703846319819639 5093672782055769479729459)
    ·
      refine ⟨7640509173083654219594189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5093672782055769479729459 7640509173083654219594189)
      ·
        refine ⟨2865190939906370332347821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7640509173083654219594189 2865190939906370332347821)
        ·
          refine ⟨1074446602464888874630433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2865190939906370332347821 1074446602464888874630433)
          ·
            refine ⟨805834951848666655972825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1074446602464888874630433 805834951848666655972825)
            ·
              refine ⟨604376213886499991979619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 805834951848666655972825 604376213886499991979619)
              ·
                refine ⟨906564320829749987969429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 604376213886499991979619 906564320829749987969429)
                ·
                  refine ⟨42495202538894530686067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 906564320829749987969429 42495202538894530686067)
                  ·
                    rfl

theorem cell21_186208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 6].length) (baseStart_186208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_186208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_186208 prefixEnd_186208 := by exact prefixLift 186208
  have htrace : WordTrace (prefixWord ++ tailWord_186208) baseStart_186208 baseEnd_186208 := by
    simpa [prefixWord, tailWord_186208, baseEnd_186208] using wordTrace_append hprefix tailTrace_186208
  have hstable : (prefixWord ++ tailWord_186208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186208).length < 2 ^ (prefixWord ++ tailWord_186208).sum := by decide
  have hdescent : baseEnd_186208 < baseStart_186208 := by decide
  rcases family_descends (prefixWord ++ tailWord_186208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186211 : List Nat := [1, 1, 1, 5, 4, 2, 1, 1, 5]
def baseStart_186211 : Nat := 118140960795 + 186211 * 2 ^ 59
def prefixEnd_186211 : Nat := 4983230072969 + 3 ^ 40 * 186211 * 2
def baseEnd_186211 : Nat := 42495887179767192136061

theorem tailTrace_186211 : CollatzResearch.WordTrace tailWord_186211 prefixEnd_186211 42495887179767192136061 := by
  unfold tailWord_186211
  simp only [CollatzResearch.WordTrace]
  refine ⟨6791673128396824151998487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4527782085597882767998991 6791673128396824151998487)
  ·
    refine ⟨10187509692595236227997731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6791673128396824151998487 10187509692595236227997731)
    ·
      refine ⟨15281264538892854341996597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10187509692595236227997731 15281264538892854341996597)
      ·
        refine ⟨1432618550521205094562181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15281264538892854341996597 1432618550521205094562181)
        ·
          refine ⟨268615978222725955230409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1432618550521205094562181 268615978222725955230409)
          ·
            refine ⟨201461983667044466422807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268615978222725955230409 201461983667044466422807)
            ·
              refine ⟨302192975500566699634211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201461983667044466422807 302192975500566699634211)
              ·
                refine ⟨453289463250850049451317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302192975500566699634211 453289463250850049451317)
                ·
                  refine ⟨42495887179767192136061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 453289463250850049451317 42495887179767192136061)
                  ·
                    rfl

theorem cell21_186211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 5].length) (baseStart_186211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_186211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_186211 prefixEnd_186211 := by exact prefixLift 186211
  have htrace : WordTrace (prefixWord ++ tailWord_186211) baseStart_186211 baseEnd_186211 := by
    simpa [prefixWord, tailWord_186211, baseEnd_186211] using wordTrace_append hprefix tailTrace_186211
  have hstable : (prefixWord ++ tailWord_186211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186211).length < 2 ^ (prefixWord ++ tailWord_186211).sum := by decide
  have hdescent : baseEnd_186211 < baseStart_186211 := by decide
  rcases family_descends (prefixWord ++ tailWord_186211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186262 : List Nat := [5, 3, 1, 1, 2, 1, 1, 4, 3]
def baseStart_186262 : Nat := 118140960795 + 186262 * 2 ^ 59
def prefixEnd_186262 : Nat := 4983230072969 + 3 ^ 40 * 186262 * 2
def baseEnd_186262 : Nat := 42507526074602436785957

theorem tailTrace_186262 : CollatzResearch.WordTrace tailWord_186262 prefixEnd_186262 42507526074602436785957 := by
  unfold tailWord_186262
  simp only [CollatzResearch.WordTrace]
  refine ⟨424595828200753741381565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4529022167474706574736693 424595828200753741381565)
  ·
    refine ⟨159223435575282653018087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 424595828200753741381565 159223435575282653018087)
    ·
      refine ⟨238835153362923979527131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159223435575282653018087 238835153362923979527131)
      ·
        refine ⟨358252730044385969290697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238835153362923979527131 358252730044385969290697)
        ·
          refine ⟨268689547533289476968023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 358252730044385969290697 268689547533289476968023)
          ·
            refine ⟨403034321299934215452035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268689547533289476968023 403034321299934215452035)
            ·
              refine ⟨604551481949901323178053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403034321299934215452035 604551481949901323178053)
              ·
                refine ⟨113353402865606498095885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 604551481949901323178053 113353402865606498095885)
                ·
                  refine ⟨42507526074602436785957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113353402865606498095885 42507526074602436785957)
                  ·
                    rfl

theorem cell21_186262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_186262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_186262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_186262 prefixEnd_186262 := by exact prefixLift 186262
  have htrace : WordTrace (prefixWord ++ tailWord_186262) baseStart_186262 baseEnd_186262 := by
    simpa [prefixWord, tailWord_186262, baseEnd_186262] using wordTrace_append hprefix tailTrace_186262
  have hstable : (prefixWord ++ tailWord_186262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186262).length < 2 ^ (prefixWord ++ tailWord_186262).sum := by decide
  have hdescent : baseEnd_186262 < baseStart_186262 := by decide
  rcases family_descends (prefixWord ++ tailWord_186262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186273 : List Nat := [1, 2, 3, 4, 3, 1, 1, 6]
def baseStart_186273 : Nat := 118140960795 + 186273 * 2 ^ 59
def prefixEnd_186273 : Nat := 4983230072969 + 3 ^ 40 * 186273 * 2
def baseEnd_186273 : Nat := 14170012141489620700867

theorem tailTrace_186273 : CollatzResearch.WordTrace tailWord_186273 prefixEnd_186273 14170012141489620700867 := by
  unfold tailWord_186273
  simp only [CollatzResearch.WordTrace]
  refine ⟨6793934454172208740755473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4529289636114805827170315 6793934454172208740755473)
  ·
    refine ⟨5095450840629156555566605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6793934454172208740755473 5095450840629156555566605)
    ·
      refine ⟨1910794065235933708337477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5095450840629156555566605 1910794065235933708337477)
      ·
        refine ⟨358273887231737570313277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1910794065235933708337477 358273887231737570313277)
        ·
          refine ⟨134352707711901588867479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 358273887231737570313277 134352707711901588867479)
          ·
            refine ⟨201529061567852383301219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134352707711901588867479 201529061567852383301219)
            ·
              refine ⟨302293592351778574951829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201529061567852383301219 302293592351778574951829)
              ·
                refine ⟨14170012141489620700867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 302293592351778574951829 14170012141489620700867)
                ·
                  rfl

theorem cell21_186273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 6].length) (baseStart_186273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_186273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_186273 prefixEnd_186273 := by exact prefixLift 186273
  have htrace : WordTrace (prefixWord ++ tailWord_186273) baseStart_186273 baseEnd_186273 := by
    simpa [prefixWord, tailWord_186273, baseEnd_186273] using wordTrace_append hprefix tailTrace_186273
  have hstable : (prefixWord ++ tailWord_186273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186273).length < 2 ^ (prefixWord ++ tailWord_186273).sum := by decide
  have hdescent : baseEnd_186273 < baseStart_186273 := by decide
  rcases family_descends (prefixWord ++ tailWord_186273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186394 : List Nat := [3, 1, 1, 3, 1, 5, 2, 1, 4]
def baseStart_186394 : Nat := 118140960795 + 186394 * 2 ^ 59
def prefixEnd_186394 : Nat := 4983230072969 + 3 ^ 40 * 186394 * 2
def baseEnd_186394 : Nat := 42537650272999540585687

theorem tailTrace_186394 : CollatzResearch.WordTrace tailWord_186394 prefixEnd_186394 42537650272999540585687 := by
  unfold tailWord_186394
  simp only [CollatzResearch.WordTrace]
  refine ⟨1699586921683461601477559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4532231791155897603940157 1699586921683461601477559)
  ·
    refine ⟨2549380382525192402216339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1699586921683461601477559 2549380382525192402216339)
    ·
      refine ⟨3824070573787788603324509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2549380382525192402216339 3824070573787788603324509)
      ·
        refine ⟨1434026465170420726246691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3824070573787788603324509 1434026465170420726246691)
        ·
          refine ⟨2151039697755631089370037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1434026465170420726246691 2151039697755631089370037)
          ·
            refine ⟨201659971664590414628441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2151039697755631089370037 201659971664590414628441)
            ·
              refine ⟨151244978748442810971331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201659971664590414628441 151244978748442810971331)
              ·
                refine ⟨226867468122664216456997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151244978748442810971331 226867468122664216456997)
                ·
                  refine ⟨42537650272999540585687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 226867468122664216456997 42537650272999540585687)
                  ·
                    rfl

theorem cell21_186394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_186394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_186394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_186394 prefixEnd_186394 := by exact prefixLift 186394
  have htrace : WordTrace (prefixWord ++ tailWord_186394) baseStart_186394 baseEnd_186394 := by
    simpa [prefixWord, tailWord_186394, baseEnd_186394] using wordTrace_append hprefix tailTrace_186394
  have hstable : (prefixWord ++ tailWord_186394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186394).length < 2 ^ (prefixWord ++ tailWord_186394).sum := by decide
  have hdescent : baseEnd_186394 < baseStart_186394 := by decide
  rcases family_descends (prefixWord ++ tailWord_186394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186419 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 8]
def baseStart_186419 : Nat := 118140960795 + 186419 * 2 ^ 59
def prefixEnd_186419 : Nat := 4983230072969 + 3 ^ 40 * 186419 * 2
def baseEnd_186419 : Nat := 42543355613605052668969

theorem tailTrace_186419 : CollatzResearch.WordTrace tailWord_186419 prefixEnd_186419 42543355613605052668969 := by
  unfold tailWord_186419
  simp only [CollatzResearch.WordTrace]
  refine ⟨6799259511643275675570311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4532839674428850450380207 6799259511643275675570311)
  ·
    refine ⟨10198889267464913513355467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6799259511643275675570311 10198889267464913513355467)
    ·
      refine ⟨15298333901197370270033201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10198889267464913513355467 15298333901197370270033201)
      ·
        refine ⟨11473750425898027702524901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15298333901197370270033201 11473750425898027702524901)
        ·
          refine ⟨2151328204855880194223419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11473750425898027702524901 2151328204855880194223419)
          ·
            refine ⟨3226992307283820291335129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2151328204855880194223419 3226992307283820291335129)
            ·
              refine ⟨2420244230462865218501347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3226992307283820291335129 2420244230462865218501347)
              ·
                refine ⟨3630366345694297827752021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2420244230462865218501347 3630366345694297827752021)
                ·
                  refine ⟨42543355613605052668969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3630366345694297827752021 42543355613605052668969)
                  ·
                    rfl

theorem cell21_186419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 8].length) (baseStart_186419 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_186419 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_186419 prefixEnd_186419 := by exact prefixLift 186419
  have htrace : WordTrace (prefixWord ++ tailWord_186419) baseStart_186419 baseEnd_186419 := by
    simpa [prefixWord, tailWord_186419, baseEnd_186419] using wordTrace_append hprefix tailTrace_186419
  have hstable : (prefixWord ++ tailWord_186419).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186419).length < 2 ^ (prefixWord ++ tailWord_186419).sum := by decide
  have hdescent : baseEnd_186419 < baseStart_186419 := by decide
  rcases family_descends (prefixWord ++ tailWord_186419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186532 : List Nat := [2, 3, 1, 2, 4, 2, 1, 3, 3]
def baseStart_186532 : Nat := 118140960795 + 186532 * 2 ^ 59
def prefixEnd_186532 : Nat := 4983230072969 + 3 ^ 40 * 186532 * 2
def baseEnd_186532 : Nat := 42569143753141967285405

theorem tailTrace_186532 : CollatzResearch.WordTrace tailWord_186532 prefixEnd_186532 42569143753141967285405 := by
  unfold tailWord_186532
  simp only [CollatzResearch.WordTrace]
  refine ⟨3401690480116947987216925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4535587306822597316289233 3401690480116947987216925)
  ·
    refine ⟨1275633930043855495206347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3401690480116947987216925 1275633930043855495206347)
    ·
      refine ⟨1913450895065783242809521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1275633930043855495206347 1913450895065783242809521)
      ·
        refine ⟨1435088171299337432107141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1913450895065783242809521 1435088171299337432107141)
        ·
          refine ⟨269079032118625768520089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1435088171299337432107141 269079032118625768520089)
          ·
            refine ⟨201809274088969326390067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269079032118625768520089 201809274088969326390067)
            ·
              refine ⟨302713911133453989585101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201809274088969326390067 302713911133453989585101)
              ·
                refine ⟨113517716675045246094413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 302713911133453989585101 113517716675045246094413)
                ·
                  refine ⟨42569143753141967285405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113517716675045246094413 42569143753141967285405)
                  ·
                    rfl

theorem cell21_186532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_186532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_186532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_186532 prefixEnd_186532 := by exact prefixLift 186532
  have htrace : WordTrace (prefixWord ++ tailWord_186532) baseStart_186532 baseEnd_186532 := by
    simpa [prefixWord, tailWord_186532, baseEnd_186532] using wordTrace_append hprefix tailTrace_186532
  have hstable : (prefixWord ++ tailWord_186532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186532).length < 2 ^ (prefixWord ++ tailWord_186532).sum := by decide
  have hdescent : baseEnd_186532 < baseStart_186532 := by decide
  rcases family_descends (prefixWord ++ tailWord_186532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186549 : List Nat := [1, 3, 3, 4, 1, 1, 3, 2, 3]
def baseStart_186549 : Nat := 118140960795 + 186549 * 2 ^ 59
def prefixEnd_186549 : Nat := 4983230072969 + 3 ^ 40 * 186549 * 2
def baseEnd_186549 : Nat := 42573023384753715502037

theorem tailTrace_186549 : CollatzResearch.WordTrace tailWord_186549 prefixEnd_186549 42573023384753715502037 := by
  unfold tailWord_186549
  simp only [CollatzResearch.WordTrace]
  refine ⟨6804001001172307877802701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4536000667448205251868467 6804001001172307877802701)
  ·
    refine ⟨2551500375439615454176013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6804001001172307877802701 2551500375439615454176013)
    ·
      refine ⟨956812640789855795316005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2551500375439615454176013 956812640789855795316005)
      ·
        refine ⟨179402370148097961621751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 956812640789855795316005 179402370148097961621751)
        ·
          refine ⟨269103555222146942432627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179402370148097961621751 269103555222146942432627)
          ·
            refine ⟨403655332833220413648941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269103555222146942432627 403655332833220413648941)
            ·
              refine ⟨151370749812457655118353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 403655332833220413648941 151370749812457655118353)
              ·
                refine ⟨113528062359343241338765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151370749812457655118353 113528062359343241338765)
                ·
                  refine ⟨42573023384753715502037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113528062359343241338765 42573023384753715502037)
                  ·
                    rfl

theorem cell21_186549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2, 3].length) (baseStart_186549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_186549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_186549 prefixEnd_186549 := by exact prefixLift 186549
  have htrace : WordTrace (prefixWord ++ tailWord_186549) baseStart_186549 baseEnd_186549 := by
    simpa [prefixWord, tailWord_186549, baseEnd_186549] using wordTrace_append hprefix tailTrace_186549
  have hstable : (prefixWord ++ tailWord_186549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186549).length < 2 ^ (prefixWord ++ tailWord_186549).sum := by decide
  have hdescent : baseEnd_186549 < baseStart_186549 := by decide
  rcases family_descends (prefixWord ++ tailWord_186549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186616 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 9]
def baseStart_186616 : Nat := 118140960795 + 186616 * 2 ^ 59
def prefixEnd_186616 : Nat := 4983230072969 + 3 ^ 40 * 186616 * 2
def baseEnd_186616 : Nat := 42588313697576487885233

theorem tailTrace_186616 : CollatzResearch.WordTrace tailWord_186616 prefixEnd_186616 42588313697576487885233 := by
  unfold tailWord_186616
  simp only [CollatzResearch.WordTrace]
  refine ⟨3403222345964789160245851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4537629794619718880327801 3403222345964789160245851)
  ·
    refine ⟨5104833518947183740368777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3403222345964789160245851 5104833518947183740368777)
    ·
      refine ⟨3828625139210387805276583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5104833518947183740368777 3828625139210387805276583)
      ·
        refine ⟨5742937708815581707914875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3828625139210387805276583 5742937708815581707914875)
        ·
          refine ⟨8614406563223372561872313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5742937708815581707914875 8614406563223372561872313)
          ·
            refine ⟨6460804922417529421404235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8614406563223372561872313 6460804922417529421404235)
            ·
              refine ⟨9691207383626294132106353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6460804922417529421404235 9691207383626294132106353)
              ·
                refine ⟨7268405537719720599079765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9691207383626294132106353 7268405537719720599079765)
                ·
                  refine ⟨42588313697576487885233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7268405537719720599079765 42588313697576487885233)
                  ·
                    rfl

theorem cell21_186616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_186616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_186616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_186616 prefixEnd_186616 := by exact prefixLift 186616
  have htrace : WordTrace (prefixWord ++ tailWord_186616) baseStart_186616 baseEnd_186616 := by
    simpa [prefixWord, tailWord_186616, baseEnd_186616] using wordTrace_append hprefix tailTrace_186616
  have hstable : (prefixWord ++ tailWord_186616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186616).length < 2 ^ (prefixWord ++ tailWord_186616).sum := by decide
  have hdescent : baseEnd_186616 < baseStart_186616 := by decide
  rcases family_descends (prefixWord ++ tailWord_186616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186633 : List Nat := [1, 2, 1, 1, 3, 5, 1, 2, 5]
def baseStart_186633 : Nat := 118140960795 + 186633 * 2 ^ 59
def prefixEnd_186633 : Nat := 4983230072969 + 3 ^ 40 * 186633 * 2
def baseEnd_186633 : Nat := 42592193329188236101865

theorem tailTrace_186633 : CollatzResearch.WordTrace tailWord_186633 prefixEnd_186633 42592193329188236101865 := by
  unfold tailWord_186633
  simp only [CollatzResearch.WordTrace]
  refine ⟨6807064732867990223860553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4538043155245326815907035 6807064732867990223860553)
  ·
    refine ⟨5105298549650992667895415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6807064732867990223860553 5105298549650992667895415)
    ·
      refine ⟨7657947824476489001843123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5105298549650992667895415 7657947824476489001843123)
      ·
        refine ⟨11486921736714733502764685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7657947824476489001843123 11486921736714733502764685)
        ·
          refine ⟨4307595651268025063536757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11486921736714733502764685 4307595651268025063536757)
          ·
            refine ⟨403837092306377349706571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4307595651268025063536757 403837092306377349706571)
            ·
              refine ⟨605755638459566024559857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403837092306377349706571 605755638459566024559857)
              ·
                refine ⟨454316728844674518419893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605755638459566024559857 454316728844674518419893)
                ·
                  refine ⟨42592193329188236101865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 454316728844674518419893 42592193329188236101865)
                  ·
                    rfl

theorem cell21_186633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 5].length) (baseStart_186633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_186633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_186633 prefixEnd_186633 := by exact prefixLift 186633
  have htrace : WordTrace (prefixWord ++ tailWord_186633) baseStart_186633 baseEnd_186633 := by
    simpa [prefixWord, tailWord_186633, baseEnd_186633] using wordTrace_append hprefix tailTrace_186633
  have hstable : (prefixWord ++ tailWord_186633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186633).length < 2 ^ (prefixWord ++ tailWord_186633).sum := by decide
  have hdescent : baseEnd_186633 < baseStart_186633 := by decide
  rcases family_descends (prefixWord ++ tailWord_186633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186718 : List Nat := [4, 4, 2, 1, 1, 2, 1, 1, 5]
def baseStart_186718 : Nat := 118140960795 + 186718 * 2 ^ 59
def prefixEnd_186718 : Nat := 4983230072969 + 3 ^ 40 * 186718 * 2
def baseEnd_186718 : Nat := 42611591487246977185025

theorem tailTrace_186718 : CollatzResearch.WordTrace tailWord_186718 prefixEnd_186718 42611591487246977185025 := by
  unfold tailWord_186718
  simp only [CollatzResearch.WordTrace]
  refine ⟨851270617195006217588101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4540109958373366493803205 851270617195006217588101)
  ·
    refine ⟨159613240724063665797769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 851270617195006217588101 159613240724063665797769)
    ·
      refine ⟨119709930543047749348327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159613240724063665797769 119709930543047749348327)
      ·
        refine ⟨179564895814571624022491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119709930543047749348327 179564895814571624022491)
        ·
          refine ⟨269347343721857436033737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179564895814571624022491 269347343721857436033737)
          ·
            refine ⟨202010507791393077025303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269347343721857436033737 202010507791393077025303)
            ·
              refine ⟨303015761687089615537955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202010507791393077025303 303015761687089615537955)
              ·
                refine ⟨454523642530634423306933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303015761687089615537955 454523642530634423306933)
                ·
                  refine ⟨42611591487246977185025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 454523642530634423306933 42611591487246977185025)
                  ·
                    rfl

theorem cell21_186718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_186718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_186718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_186718 prefixEnd_186718 := by exact prefixLift 186718
  have htrace : WordTrace (prefixWord ++ tailWord_186718) baseStart_186718 baseEnd_186718 := by
    simpa [prefixWord, tailWord_186718, baseEnd_186718] using wordTrace_append hprefix tailTrace_186718
  have hstable : (prefixWord ++ tailWord_186718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186718).length < 2 ^ (prefixWord ++ tailWord_186718).sum := by decide
  have hdescent : baseEnd_186718 < baseStart_186718 := by decide
  rcases family_descends (prefixWord ++ tailWord_186718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186723 : List Nat := [1, 1, 1, 5, 2, 1, 1, 3, 6]
def baseStart_186723 : Nat := 118140960795 + 186723 * 2 ^ 59
def prefixEnd_186723 : Nat := 4983230072969 + 3 ^ 40 * 186723 * 2
def baseEnd_186723 : Nat := 42612732555368079601681

theorem tailTrace_186723 : CollatzResearch.WordTrace tailWord_186723 prefixEnd_186723 42612732555368079601681 := by
  unfold tailWord_186723
  simp only [CollatzResearch.WordTrace]
  refine ⟨6810347302541935594636823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4540231535027957063091215 6810347302541935594636823)
  ·
    refine ⟨10215520953812903391955235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6810347302541935594636823 10215520953812903391955235)
    ·
      refine ⟨15323281430719355087932853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10215520953812903391955235 15323281430719355087932853)
      ·
        refine ⟨1436557634129939539493705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15323281430719355087932853 1436557634129939539493705)
        ·
          refine ⟨1077418225597454654620279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1436557634129939539493705 1077418225597454654620279)
          ·
            refine ⟨1616127338396181981930419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1077418225597454654620279 1616127338396181981930419)
            ·
              refine ⟨2424191007594272972895629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1616127338396181981930419 2424191007594272972895629)
              ·
                refine ⟨909071627847852364835861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2424191007594272972895629 909071627847852364835861)
                ·
                  refine ⟨42612732555368079601681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 909071627847852364835861 42612732555368079601681)
                  ·
                    rfl

theorem cell21_186723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 6].length) (baseStart_186723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_186723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_186723 prefixEnd_186723 := by exact prefixLift 186723
  have htrace : WordTrace (prefixWord ++ tailWord_186723) baseStart_186723 baseEnd_186723 := by
    simpa [prefixWord, tailWord_186723, baseEnd_186723] using wordTrace_append hprefix tailTrace_186723
  have hstable : (prefixWord ++ tailWord_186723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186723).length < 2 ^ (prefixWord ++ tailWord_186723).sum := by decide
  have hdescent : baseEnd_186723 < baseStart_186723 := by decide
  rcases family_descends (prefixWord ++ tailWord_186723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186909 : List Nat := [1, 4, 2, 2, 1, 2, 4, 1, 4]
def baseStart_186909 : Nat := 118140960795 + 186909 * 2 ^ 59
def prefixEnd_186909 : Nat := 4983230072969 + 3 ^ 40 * 186909 * 2
def baseEnd_186909 : Nat := 42655180289473089501301

theorem tailTrace_186909 : CollatzResearch.WordTrace tailWord_186909 prefixEnd_186909 42655180289473089501301 := by
  unfold tailWord_186909
  simp only [CollatzResearch.WordTrace]
  refine ⟨6817131279868089360907781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4544754186578726240605187 6817131279868089360907781)
  ·
    refine ⟨1278212114975266755170209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6817131279868089360907781 1278212114975266755170209)
    ·
      refine ⟨958659086231450066377657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1278212114975266755170209 958659086231450066377657)
      ·
        refine ⟨718994314673587549783243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 958659086231450066377657 718994314673587549783243)
        ·
          refine ⟨1078491472010381324674865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 718994314673587549783243 1078491472010381324674865)
          ·
            refine ⟨808868604007785993506149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1078491472010381324674865 808868604007785993506149)
            ·
              refine ⟨151662863251459873782403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 808868604007785993506149 151662863251459873782403)
              ·
                refine ⟨227494294877189810673605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151662863251459873782403 227494294877189810673605)
                ·
                  refine ⟨42655180289473089501301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 227494294877189810673605 42655180289473089501301)
                  ·
                    rfl

theorem cell21_186909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_186909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_186909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_186909 prefixEnd_186909 := by exact prefixLift 186909
  have htrace : WordTrace (prefixWord ++ tailWord_186909) baseStart_186909 baseEnd_186909 := by
    simpa [prefixWord, tailWord_186909, baseEnd_186909] using wordTrace_append hprefix tailTrace_186909
  have hstable : (prefixWord ++ tailWord_186909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186909).length < 2 ^ (prefixWord ++ tailWord_186909).sum := by decide
  have hdescent : baseEnd_186909 < baseStart_186909 := by decide
  rcases family_descends (prefixWord ++ tailWord_186909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186954 : List Nat := [3, 1, 2, 1, 1, 5, 1, 4, 3]
def baseStart_186954 : Nat := 118140960795 + 186954 * 2 ^ 59
def prefixEnd_186954 : Nat := 4983230072969 + 3 ^ 40 * 186954 * 2
def baseEnd_186954 : Nat := 42665449902563011251209

theorem tailTrace_186954 : CollatzResearch.WordTrace tailWord_186954 prefixEnd_186954 42665449902563011251209 := by
  unfold tailWord_186954
  simp only [CollatzResearch.WordTrace]
  refine ⟨1704693141176265511573979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4545848376470041364197277 1704693141176265511573979)
  ·
    refine ⟨2557039711764398267360969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1704693141176265511573979 2557039711764398267360969)
    ·
      refine ⟨1917779783823298700520727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2557039711764398267360969 1917779783823298700520727)
      ·
        refine ⟨2876669675734948050781091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1917779783823298700520727 2876669675734948050781091)
        ·
          refine ⟨4315004513602422076171637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2876669675734948050781091 4315004513602422076171637)
          ·
            refine ⟨404531673150227069641091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4315004513602422076171637 404531673150227069641091)
            ·
              refine ⟨606797509725340604461637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404531673150227069641091 606797509725340604461637)
              ·
                refine ⟨113774533073501363336557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 606797509725340604461637 113774533073501363336557)
                ·
                  refine ⟨42665449902563011251209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113774533073501363336557 42665449902563011251209)
                  ·
                    rfl

theorem cell21_186954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4, 3].length) (baseStart_186954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_186954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_186954 prefixEnd_186954 := by exact prefixLift 186954
  have htrace : WordTrace (prefixWord ++ tailWord_186954) baseStart_186954 baseEnd_186954 := by
    simpa [prefixWord, tailWord_186954, baseEnd_186954] using wordTrace_append hprefix tailTrace_186954
  have hstable : (prefixWord ++ tailWord_186954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186954).length < 2 ^ (prefixWord ++ tailWord_186954).sum := by decide
  have hdescent : baseEnd_186954 < baseStart_186954 := by decide
  rcases family_descends (prefixWord ++ tailWord_186954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186974 : List Nat := [4, 4, 1, 2, 1, 1, 3, 5]
def baseStart_186974 : Nat := 118140960795 + 186974 * 2 ^ 59
def prefixEnd_186974 : Nat := 4983230072969 + 3 ^ 40 * 186974 * 2
def baseEnd_186974 : Nat := 14223338058349140305945

theorem tailTrace_186974 : CollatzResearch.WordTrace tailWord_186974 prefixEnd_186974 14223338058349140305945 := by
  unfold tailWord_186974
  simp only [CollatzResearch.WordTrace]
  refine ⟨852437753079075682752997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4546334683088403641349317 852437753079075682752997)
  ·
    refine ⟨159832078702326690516187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 852437753079075682752997 159832078702326690516187)
    ·
      refine ⟨239748118053490035774281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159832078702326690516187 239748118053490035774281)
      ·
        refine ⟨179811088540117526830711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239748118053490035774281 179811088540117526830711)
        ·
          refine ⟨269716632810176290246067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179811088540117526830711 269716632810176290246067)
          ·
            refine ⟨404574949215264435369101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269716632810176290246067 404574949215264435369101)
            ·
              refine ⟨151715605955724163263413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 404574949215264435369101 151715605955724163263413)
              ·
                refine ⟨14223338058349140305945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 151715605955724163263413 14223338058349140305945)
                ·
                  rfl

theorem cell21_186974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_186974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_186974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_186974 prefixEnd_186974 := by exact prefixLift 186974
  have htrace : WordTrace (prefixWord ++ tailWord_186974) baseStart_186974 baseEnd_186974 := by
    simpa [prefixWord, tailWord_186974, baseEnd_186974] using wordTrace_append hprefix tailTrace_186974
  have hstable : (prefixWord ++ tailWord_186974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186974).length < 2 ^ (prefixWord ++ tailWord_186974).sum := by decide
  have hdescent : baseEnd_186974 < baseStart_186974 := by decide
  rcases family_descends (prefixWord ++ tailWord_186974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187013 : List Nat := [1, 3, 1, 1, 4, 3, 2, 1, 5]
def baseStart_187013 : Nat := 118140960795 + 187013 * 2 ^ 59
def prefixEnd_187013 : Nat := 4983230072969 + 3 ^ 40 * 187013 * 2
def baseEnd_187013 : Nat := 42678914506392019767755

theorem tailTrace_187013 : CollatzResearch.WordTrace tailWord_187013 prefixEnd_187013 42678914506392019767755 := by
  unfold tailWord_187013
  simp only [CollatzResearch.WordTrace]
  refine ⟨6820924471491315122693693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4547282980994210081795795 6820924471491315122693693)
  ·
    refine ⟨2557846676809243171010135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6820924471491315122693693 2557846676809243171010135)
    ·
      refine ⟨3836770015213864756515203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2557846676809243171010135 3836770015213864756515203)
      ·
        refine ⟨5755155022820797134772805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3836770015213864756515203 5755155022820797134772805)
        ·
          refine ⟨1079091566778899462769901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5755155022820797134772805 1079091566778899462769901)
          ·
            refine ⟨404659337542087298538713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1079091566778899462769901 404659337542087298538713)
            ·
              refine ⟨303494503156565473904035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404659337542087298538713 303494503156565473904035)
              ·
                refine ⟨455241754734848210856053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303494503156565473904035 455241754734848210856053)
                ·
                  refine ⟨42678914506392019767755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 455241754734848210856053 42678914506392019767755)
                  ·
                    rfl

theorem cell21_187013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_187013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_187013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_187013 prefixEnd_187013 := by exact prefixLift 187013
  have htrace : WordTrace (prefixWord ++ tailWord_187013) baseStart_187013 baseEnd_187013 := by
    simpa [prefixWord, tailWord_187013, baseEnd_187013] using wordTrace_append hprefix tailTrace_187013
  have hstable : (prefixWord ++ tailWord_187013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187013).length < 2 ^ (prefixWord ++ tailWord_187013).sum := by decide
  have hdescent : baseEnd_187013 < baseStart_187013 := by decide
  rcases family_descends (prefixWord ++ tailWord_187013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187182 : List Nat := [4, 1, 3, 2, 1, 2, 2, 1, 5]
def baseStart_187182 : Nat := 118140960795 + 187182 * 2 ^ 59
def prefixEnd_187182 : Nat := 4983230072969 + 3 ^ 40 * 187182 * 2
def baseEnd_187182 : Nat := 42717482608885281450743

theorem tailTrace_187182 : CollatzResearch.WordTrace tailWord_187182 prefixEnd_187182 42717482608885281450743 := by
  unfold tailWord_187182
  simp only [CollatzResearch.WordTrace]
  refine ⟨853386050984882123199475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4551392271919371323730533 853386050984882123199475)
  ·
    refine ⟨1280079076477323184799213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 853386050984882123199475 1280079076477323184799213)
    ·
      refine ⟨480029653678996194299705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1280079076477323184799213 480029653678996194299705)
      ·
        refine ⟨360022240259247145724779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 480029653678996194299705 360022240259247145724779)
        ·
          refine ⟨540033360388870718587169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360022240259247145724779 540033360388870718587169)
          ·
            refine ⟨405025020291653038940377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 540033360388870718587169 405025020291653038940377)
            ·
              refine ⟨303768765218739779205283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 405025020291653038940377 303768765218739779205283)
              ·
                refine ⟨455653147828109668807925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303768765218739779205283 455653147828109668807925)
                ·
                  refine ⟨42717482608885281450743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 455653147828109668807925 42717482608885281450743)
                  ·
                    rfl

theorem cell21_187182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_187182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_187182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_187182 prefixEnd_187182 := by exact prefixLift 187182
  have htrace : WordTrace (prefixWord ++ tailWord_187182) baseStart_187182 baseEnd_187182 := by
    simpa [prefixWord, tailWord_187182, baseEnd_187182] using wordTrace_append hprefix tailTrace_187182
  have hstable : (prefixWord ++ tailWord_187182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187182).length < 2 ^ (prefixWord ++ tailWord_187182).sum := by decide
  have hdescent : baseEnd_187182 < baseStart_187182 := by decide
  rcases family_descends (prefixWord ++ tailWord_187182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187269 : List Nat := [1, 3, 1, 1, 3, 3, 2, 7]
def baseStart_187269 : Nat := 118140960795 + 187269 * 2 ^ 59
def prefixEnd_187269 : Nat := 4983230072969 + 3 ^ 40 * 187269 * 2
def baseEnd_187269 : Nat := 14245779064730821166855

theorem tailTrace_187269 : CollatzResearch.WordTrace tailWord_187269 prefixEnd_187269 14245779064730821166855 := by
  unfold tailWord_187269
  simp only [CollatzResearch.WordTrace]
  refine ⟨6830261558563870844012861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4553507705709247229341907 6830261558563870844012861)
  ·
    refine ⟨2561348084461451566504823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6830261558563870844012861 2561348084461451566504823)
    ·
      refine ⟨3842022126692177349757235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2561348084461451566504823 3842022126692177349757235)
      ·
        refine ⟨5763033190038266024635853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3842022126692177349757235 5763033190038266024635853)
        ·
          refine ⟨2161137446264349759238445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5763033190038266024635853 2161137446264349759238445)
          ·
            refine ⟨810426542349131159714417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2161137446264349759238445 810426542349131159714417)
            ·
              refine ⟨607819906761848369785813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 810426542349131159714417 607819906761848369785813)
              ·
                refine ⟨14245779064730821166855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 607819906761848369785813 14245779064730821166855)
                ·
                  rfl

theorem cell21_187269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 7].length) (baseStart_187269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_187269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_187269 prefixEnd_187269 := by exact prefixLift 187269
  have htrace : WordTrace (prefixWord ++ tailWord_187269) baseStart_187269 baseEnd_187269 := by
    simpa [prefixWord, tailWord_187269, baseEnd_187269] using wordTrace_append hprefix tailTrace_187269
  have hstable : (prefixWord ++ tailWord_187269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187269).length < 2 ^ (prefixWord ++ tailWord_187269).sum := by decide
  have hdescent : baseEnd_187269 < baseStart_187269 := by decide
  rcases family_descends (prefixWord ++ tailWord_187269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187283 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 9]
def baseStart_187283 : Nat := 118140960795 + 187283 * 2 ^ 59
def prefixEnd_187283 : Nat := 4983230072969 + 3 ^ 40 * 187283 * 2
def baseEnd_187283 : Nat := 42740532184931550267203

theorem tailTrace_187283 : CollatzResearch.WordTrace tailWord_187283 prefixEnd_187283 42740532184931550267203 := by
  unfold tailWord_187283
  simp only [CollatzResearch.WordTrace]
  refine ⟨6830772180513151235022503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4553848120342100823348335 6830772180513151235022503)
  ·
    refine ⟨10246158270769726852533755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6830772180513151235022503 10246158270769726852533755)
    ·
      refine ⟨15369237406154590278800633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10246158270769726852533755 15369237406154590278800633)
      ·
        refine ⟨11526928054615942709100475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15369237406154590278800633 11526928054615942709100475)
        ·
          refine ⟨17290392081923914063650713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11526928054615942709100475 17290392081923914063650713)
          ·
            refine ⟨12967794061442935547738035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17290392081923914063650713 12967794061442935547738035)
            ·
              refine ⟨19451691092164403321607053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12967794061442935547738035 19451691092164403321607053)
              ·
                refine ⟨7294384159561651245602645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19451691092164403321607053 7294384159561651245602645)
                ·
                  refine ⟨42740532184931550267203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7294384159561651245602645 42740532184931550267203)
                  ·
                    rfl

theorem cell21_187283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 9].length) (baseStart_187283 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_187283 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_187283 prefixEnd_187283 := by exact prefixLift 187283
  have htrace : WordTrace (prefixWord ++ tailWord_187283) baseStart_187283 baseEnd_187283 := by
    simpa [prefixWord, tailWord_187283, baseEnd_187283] using wordTrace_append hprefix tailTrace_187283
  have hstable : (prefixWord ++ tailWord_187283).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187283).length < 2 ^ (prefixWord ++ tailWord_187283).sum := by decide
  have hdescent : baseEnd_187283 < baseStart_187283 := by decide
  rcases family_descends (prefixWord ++ tailWord_187283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187292 : List Nat := [2, 2, 3, 3, 2, 2, 2, 2, 3]
def baseStart_187292 : Nat := 118140960795 + 187292 * 2 ^ 59
def prefixEnd_187292 : Nat := 4983230072969 + 3 ^ 40 * 187292 * 2
def baseEnd_187292 : Nat := 42742586107549534617185

theorem tailTrace_187292 : CollatzResearch.WordTrace tailWord_187292 prefixEnd_187292 42742586107549534617185 := by
  unfold tailWord_187292
  simp only [CollatzResearch.WordTrace]
  refine ⟨3415550218740272886050065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4554066958320363848066753 3415550218740272886050065)
  ·
    refine ⟨2561662664055204664537549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3415550218740272886050065 2561662664055204664537549)
    ·
      refine ⟨960623499020701749201581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2561662664055204664537549 960623499020701749201581)
      ·
        refine ⟨360233812132763155950593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 960623499020701749201581 360233812132763155950593)
        ·
          refine ⟨270175359099572366962945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360233812132763155950593 270175359099572366962945)
          ·
            refine ⟨202631519324679275222209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270175359099572366962945 202631519324679275222209)
            ·
              refine ⟨151973639493509456416657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202631519324679275222209 151973639493509456416657)
              ·
                refine ⟨113980229620132092312493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151973639493509456416657 113980229620132092312493)
                ·
                  refine ⟨42742586107549534617185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113980229620132092312493 42742586107549534617185)
                  ·
                    rfl

theorem cell21_187292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 3].length) (baseStart_187292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_187292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_187292 prefixEnd_187292 := by exact prefixLift 187292
  have htrace : WordTrace (prefixWord ++ tailWord_187292) baseStart_187292 baseEnd_187292 := by
    simpa [prefixWord, tailWord_187292, baseEnd_187292] using wordTrace_append hprefix tailTrace_187292
  have hstable : (prefixWord ++ tailWord_187292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187292).length < 2 ^ (prefixWord ++ tailWord_187292).sum := by decide
  have hdescent : baseEnd_187292 < baseStart_187292 := by decide
  rcases family_descends (prefixWord ++ tailWord_187292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187300 : List Nat := [2, 3, 1, 2, 1, 2, 2, 3, 5]
def baseStart_187300 : Nat := 118140960795 + 187300 * 2 ^ 59
def prefixEnd_187300 : Nat := 4983230072969 + 3 ^ 40 * 187300 * 2
def baseEnd_187300 : Nat := 42744411816543298483835

theorem tailTrace_187300 : CollatzResearch.WordTrace tailWord_187300 prefixEnd_187300 42744411816543298483835 := by
  unfold tailWord_187300
  simp only [CollatzResearch.WordTrace]
  refine ⟨3415696110725781569195677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4554261480967708758927569 3415696110725781569195677)
  ·
    refine ⟨1280886041522168088448379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3415696110725781569195677 1280886041522168088448379)
    ·
      refine ⟨1921329062283252132672569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1280886041522168088448379 1921329062283252132672569)
      ·
        refine ⟨1440996796712439099504427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1921329062283252132672569 1440996796712439099504427)
        ·
          refine ⟨2161495195068658649256641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1440996796712439099504427 2161495195068658649256641)
          ·
            refine ⟨1621121396301493986942481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2161495195068658649256641 1621121396301493986942481)
            ·
              refine ⟨1215841047226120490206861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1621121396301493986942481 1215841047226120490206861)
              ·
                refine ⟨455940392709795183827573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1215841047226120490206861 455940392709795183827573)
                ·
                  refine ⟨42744411816543298483835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 455940392709795183827573 42744411816543298483835)
                  ·
                    rfl

theorem cell21_187300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_187300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_187300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_187300 prefixEnd_187300 := by exact prefixLift 187300
  have htrace : WordTrace (prefixWord ++ tailWord_187300) baseStart_187300 baseEnd_187300 := by
    simpa [prefixWord, tailWord_187300, baseEnd_187300] using wordTrace_append hprefix tailTrace_187300
  have hstable : (prefixWord ++ tailWord_187300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187300).length < 2 ^ (prefixWord ++ tailWord_187300).sum := by decide
  have hdescent : baseEnd_187300 < baseStart_187300 := by decide
  rcases family_descends (prefixWord ++ tailWord_187300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187303 : List Nat := [1, 1, 6, 1, 3, 2, 1, 6]
def baseStart_187303 : Nat := 118140960795 + 187303 * 2 ^ 59
def prefixEnd_187303 : Nat := 4983230072969 + 3 ^ 40 * 187303 * 2
def baseEnd_187303 : Nat := 14248365485805319977943

theorem tailTrace_187303 : CollatzResearch.WordTrace tailWord_187303 prefixEnd_187303 14248365485805319977943 := by
  unfold tailWord_187303
  simp only [CollatzResearch.WordTrace]
  refine ⟨6831501640440694650750563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4554334426960463100500375 6831501640440694650750563)
  ·
    refine ⟨10247252460661041976125845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6831501640440694650750563 10247252460661041976125845)
    ·
      refine ⟨480339959093486342630899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10247252460661041976125845 480339959093486342630899)
      ·
        refine ⟨720509938640229513946349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480339959093486342630899 720509938640229513946349)
        ·
          refine ⟨270191226990086067729881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 720509938640229513946349 270191226990086067729881)
          ·
            refine ⟨202643420242564550797411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270191226990086067729881 202643420242564550797411)
            ·
              refine ⟨303965130363846826196117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202643420242564550797411 303965130363846826196117)
              ·
                refine ⟨14248365485805319977943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 303965130363846826196117 14248365485805319977943)
                ·
                  rfl

theorem cell21_187303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 6].length) (baseStart_187303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_187303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_187303 prefixEnd_187303 := by exact prefixLift 187303
  have htrace : WordTrace (prefixWord ++ tailWord_187303) baseStart_187303 baseEnd_187303 := by
    simpa [prefixWord, tailWord_187303, baseEnd_187303] using wordTrace_append hprefix tailTrace_187303
  have hstable : (prefixWord ++ tailWord_187303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187303).length < 2 ^ (prefixWord ++ tailWord_187303).sum := by decide
  have hdescent : baseEnd_187303 < baseStart_187303 := by decide
  rcases family_descends (prefixWord ++ tailWord_187303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187314 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 10]
def baseStart_187314 : Nat := 118140960795 + 187314 * 2 ^ 59
def prefixEnd_187314 : Nat := 4983230072969 + 3 ^ 40 * 187314 * 2
def baseEnd_187314 : Nat := 42747606807282385250473

theorem tailTrace_187314 : CollatzResearch.WordTrace tailWord_187314 prefixEnd_187314 42747606807282385250473 := by
  unfold tailWord_187314
  simp only [CollatzResearch.WordTrace]
  refine ⟨1707975710850210882350249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4554601895600562352933997 1707975710850210882350249)
  ·
    refine ⟨1280981783137658161762687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1707975710850210882350249 1280981783137658161762687)
    ·
      refine ⟨1921472674706487242644031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1280981783137658161762687 1921472674706487242644031)
      ·
        refine ⟨2882209012059730863966047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1921472674706487242644031 2882209012059730863966047)
        ·
          refine ⟨4323313518089596295949071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2882209012059730863966047 4323313518089596295949071)
          ·
            refine ⟨6484970277134394443923607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4323313518089596295949071 6484970277134394443923607)
            ·
              refine ⟨9727455415701591665885411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6484970277134394443923607 9727455415701591665885411)
              ·
                refine ⟨14591183123552387498828117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9727455415701591665885411 14591183123552387498828117)
                ·
                  refine ⟨42747606807282385250473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 14591183123552387498828117 42747606807282385250473)
                  ·
                    rfl

theorem cell21_187314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_187314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_187314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_187314 prefixEnd_187314 := by exact prefixLift 187314
  have htrace : WordTrace (prefixWord ++ tailWord_187314) baseStart_187314 baseEnd_187314 := by
    simpa [prefixWord, tailWord_187314, baseEnd_187314] using wordTrace_append hprefix tailTrace_187314
  have hstable : (prefixWord ++ tailWord_187314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187314).length < 2 ^ (prefixWord ++ tailWord_187314).sum := by decide
  have hdescent : baseEnd_187314 < baseStart_187314 := by decide
  rcases family_descends (prefixWord ++ tailWord_187314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187348 : List Nat := [2, 4, 1, 2, 1, 2, 3, 2, 4]
def baseStart_187348 : Nat := 118140960795 + 187348 * 2 ^ 59
def prefixEnd_187348 : Nat := 4983230072969 + 3 ^ 40 * 187348 * 2
def baseEnd_187348 : Nat := 42755366070505881683737

theorem tailTrace_187348 : CollatzResearch.WordTrace tailWord_187348 prefixEnd_187348 42755366070505881683737 := by
  unfold tailWord_187348
  simp only [CollatzResearch.WordTrace]
  refine ⟨3416571462638833668069349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4555428616851778224092465 3416571462638833668069349)
  ·
    refine ⟨640607149244781312763003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3416571462638833668069349 640607149244781312763003)
    ·
      refine ⟨960910723867171969144505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 640607149244781312763003 960910723867171969144505)
      ·
        refine ⟨720683042900378976858379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 960910723867171969144505 720683042900378976858379)
        ·
          refine ⟨1081024564350568465287569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 720683042900378976858379 1081024564350568465287569)
          ·
            refine ⟨810768423262926348965677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1081024564350568465287569 810768423262926348965677)
            ·
              refine ⟨304038158723597380862129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 810768423262926348965677 304038158723597380862129)
              ·
                refine ⟨228028619042698035646597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304038158723597380862129 228028619042698035646597)
                ·
                  refine ⟨42755366070505881683737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 228028619042698035646597 42755366070505881683737)
                  ·
                    rfl

theorem cell21_187348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_187348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_187348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_187348 prefixEnd_187348 := by exact prefixLift 187348
  have htrace : WordTrace (prefixWord ++ tailWord_187348) baseStart_187348 baseEnd_187348 := by
    simpa [prefixWord, tailWord_187348, baseEnd_187348] using wordTrace_append hprefix tailTrace_187348
  have hstable : (prefixWord ++ tailWord_187348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187348).length < 2 ^ (prefixWord ++ tailWord_187348).sum := by decide
  have hdescent : baseEnd_187348 < baseStart_187348 := by decide
  rcases family_descends (prefixWord ++ tailWord_187348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187435 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 7]
def baseStart_187435 : Nat := 118140960795 + 187435 * 2 ^ 59
def prefixEnd_187435 : Nat := 4983230072969 + 3 ^ 40 * 187435 * 2
def baseEnd_187435 : Nat := 42775220655813063733559

theorem tailTrace_187435 : CollatzResearch.WordTrace tailWord_187435 prefixEnd_187435 42775220655813063733559 := by
  unfold tailWord_187435
  simp only [CollatzResearch.WordTrace]
  refine ⟨6836316075962481194555759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4557544050641654129703839 6836316075962481194555759)
  ·
    refine ⟨10254474113943721791833639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6836316075962481194555759 10254474113943721791833639)
    ·
      refine ⟨15381711170915582687750459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10254474113943721791833639 15381711170915582687750459)
      ·
        refine ⟨23072566756373374031625689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15381711170915582687750459 23072566756373374031625689)
        ·
          refine ⟨17304425067280030523719267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23072566756373374031625689 17304425067280030523719267)
          ·
            refine ⟨25956637600920045785578901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17304425067280030523719267 25956637600920045785578901)
            ·
              refine ⟨1216717387543127146199011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25956637600920045785578901 1216717387543127146199011)
              ·
                refine ⟨1825076081314690719298517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1216717387543127146199011 1825076081314690719298517)
                ·
                  refine ⟨42775220655813063733559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1825076081314690719298517 42775220655813063733559)
                  ·
                    rfl

theorem cell21_187435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 7].length) (baseStart_187435 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_187435 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_187435 prefixEnd_187435 := by exact prefixLift 187435
  have htrace : WordTrace (prefixWord ++ tailWord_187435) baseStart_187435 baseEnd_187435 := by
    simpa [prefixWord, tailWord_187435, baseEnd_187435] using wordTrace_append hprefix tailTrace_187435
  have hstable : (prefixWord ++ tailWord_187435).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187435).length < 2 ^ (prefixWord ++ tailWord_187435).sum := by decide
  have hdescent : baseEnd_187435 < baseStart_187435 := by decide
  rcases family_descends (prefixWord ++ tailWord_187435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187466 : List Nat := [3, 1, 2, 1, 1, 2, 2, 3, 6]
def baseStart_187466 : Nat := 118140960795 + 187466 * 2 ^ 59
def prefixEnd_187466 : Nat := 4983230072969 + 3 ^ 40 * 187466 * 2
def baseEnd_187466 : Nat := 42782295278163898716829

theorem tailTrace_187466 : CollatzResearch.WordTrace tailWord_187466 prefixEnd_187466 42782295278163898716829 := by
  unfold tailWord_187466
  simp only [CollatzResearch.WordTrace]
  refine ⟨1709361684712543372233563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4558297825900115659289501 1709361684712543372233563)
  ·
    refine ⟨2564042527068815058350345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1709361684712543372233563 2564042527068815058350345)
    ·
      refine ⟨1923031895301611293762759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2564042527068815058350345 1923031895301611293762759)
      ·
        refine ⟨2884547842952416940644139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1923031895301611293762759 2884547842952416940644139)
        ·
          refine ⟨4326821764428625410966209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2884547842952416940644139 4326821764428625410966209)
          ·
            refine ⟨3245116323321469058224657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4326821764428625410966209 3245116323321469058224657)
            ·
              refine ⟨2433837242491101793668493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3245116323321469058224657 2433837242491101793668493)
              ·
                refine ⟨912688965934163172625685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2433837242491101793668493 912688965934163172625685)
                ·
                  refine ⟨42782295278163898716829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 912688965934163172625685 42782295278163898716829)
                  ·
                    rfl

theorem cell21_187466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_187466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_187466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_187466 prefixEnd_187466 := by exact prefixLift 187466
  have htrace : WordTrace (prefixWord ++ tailWord_187466) baseStart_187466 baseEnd_187466 := by
    simpa [prefixWord, tailWord_187466, baseEnd_187466] using wordTrace_append hprefix tailTrace_187466
  have hstable : (prefixWord ++ tailWord_187466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187466).length < 2 ^ (prefixWord ++ tailWord_187466).sum := by decide
  have hdescent : baseEnd_187466 < baseStart_187466 := by decide
  rcases family_descends (prefixWord ++ tailWord_187466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187486 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 7]
def baseStart_187486 : Nat := 118140960795 + 187486 * 2 ^ 59
def prefixEnd_187486 : Nat := 4983230072969 + 3 ^ 40 * 187486 * 2
def baseEnd_187486 : Nat := 42786859550648308383455

theorem tailTrace_187486 : CollatzResearch.WordTrace tailWord_187486 prefixEnd_187486 42786859550648308383455 := by
  unfold tailWord_187486
  simp only [CollatzResearch.WordTrace]
  refine ⟨854772024847214613082789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4558784132518477936441541 854772024847214613082789)
  ·
    refine ⟨160269754658852739953023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 854772024847214613082789 160269754658852739953023)
    ·
      refine ⟨240404631988279109929535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160269754658852739953023 240404631988279109929535)
      ·
        refine ⟨360606947982418664894303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240404631988279109929535 360606947982418664894303)
        ·
          refine ⟨540910421973627997341455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360606947982418664894303 540910421973627997341455)
          ·
            refine ⟨811365632960441996012183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540910421973627997341455 811365632960441996012183)
            ·
              refine ⟨1217048449440662994018275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 811365632960441996012183 1217048449440662994018275)
              ·
                refine ⟨1825572674160994491027413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1217048449440662994018275 1825572674160994491027413)
                ·
                  refine ⟨42786859550648308383455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1825572674160994491027413 42786859550648308383455)
                  ·
                    rfl

theorem cell21_187486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_187486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_187486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_187486 prefixEnd_187486 := by exact prefixLift 187486
  have htrace : WordTrace (prefixWord ++ tailWord_187486) baseStart_187486 baseEnd_187486 := by
    simpa [prefixWord, tailWord_187486, baseEnd_187486] using wordTrace_append hprefix tailTrace_187486
  have hstable : (prefixWord ++ tailWord_187486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187486).length < 2 ^ (prefixWord ++ tailWord_187486).sum := by decide
  have hdescent : baseEnd_187486 < baseStart_187486 := by decide
  rcases family_descends (prefixWord ++ tailWord_187486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187511 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 7]
def baseStart_187511 : Nat := 118140960795 + 187511 * 2 ^ 59
def prefixEnd_187511 : Nat := 4983230072969 + 3 ^ 40 * 187511 * 2
def baseEnd_187511 : Nat := 42792564891253820466737

theorem tailTrace_187511 : CollatzResearch.WordTrace tailWord_187511 prefixEnd_187511 42792564891253820466737 := by
  unfold tailWord_187511
  simp only [CollatzResearch.WordTrace]
  refine ⟨6839088023687146174322387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4559392015791430782881591 6839088023687146174322387)
  ·
    refine ⟨10258632035530719261483581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6839088023687146174322387 10258632035530719261483581)
    ·
      refine ⟨3846987013324019723056343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10258632035530719261483581 3846987013324019723056343)
      ·
        refine ⟨5770480519986029584584515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3846987013324019723056343 5770480519986029584584515)
        ·
          refine ⟨8655720779979044376876773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5770480519986029584584515 8655720779979044376876773)
          ·
            refine ⟨1622947646246070820664395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8655720779979044376876773 1622947646246070820664395)
            ·
              refine ⟨2434421469369106230996593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1622947646246070820664395 2434421469369106230996593)
              ·
                refine ⟨1825816102026829673247445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2434421469369106230996593 1825816102026829673247445)
                ·
                  refine ⟨42792564891253820466737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1825816102026829673247445 42792564891253820466737)
                  ·
                    rfl

theorem cell21_187511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 7].length) (baseStart_187511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_187511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_187511 prefixEnd_187511 := by exact prefixLift 187511
  have htrace : WordTrace (prefixWord ++ tailWord_187511) baseStart_187511 baseEnd_187511 := by
    simpa [prefixWord, tailWord_187511, baseEnd_187511] using wordTrace_append hprefix tailTrace_187511
  have hstable : (prefixWord ++ tailWord_187511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187511).length < 2 ^ (prefixWord ++ tailWord_187511).sum := by decide
  have hdescent : baseEnd_187511 < baseStart_187511 := by decide
  rcases family_descends (prefixWord ++ tailWord_187511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187559 : List Nat := [1, 1, 6, 2, 1, 1, 1, 2, 6]
def baseStart_187559 : Nat := 118140960795 + 187559 * 2 ^ 59
def prefixEnd_187559 : Nat := 4983230072969 + 3 ^ 40 * 187559 * 2
def baseEnd_187559 : Nat := 42803519145216403666639

theorem tailTrace_187559 : CollatzResearch.WordTrace tailWord_187559 prefixEnd_187559 42803519145216403666639 := by
  unfold tailWord_187559
  simp only [CollatzResearch.WordTrace]
  refine ⟨6840838727513250372069731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4560559151675500248046487 6840838727513250372069731)
  ·
    refine ⟨10261258091269875558104597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6840838727513250372069731 10261258091269875558104597)
    ·
      refine ⟨480996473028275416786153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10261258091269875558104597 480996473028275416786153)
      ·
        refine ⟨360747354771206562589615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 480996473028275416786153 360747354771206562589615)
        ·
          refine ⟨541121032156809843884423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360747354771206562589615 541121032156809843884423)
          ·
            refine ⟨811681548235214765826635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541121032156809843884423 811681548235214765826635)
            ·
              refine ⟨1217522322352822148739953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 811681548235214765826635 1217522322352822148739953)
              ·
                refine ⟨913141741764616611554965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1217522322352822148739953 913141741764616611554965)
                ·
                  refine ⟨42803519145216403666639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 913141741764616611554965 42803519145216403666639)
                  ·
                    rfl

theorem cell21_187559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 6].length) (baseStart_187559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_187559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_187559 prefixEnd_187559 := by exact prefixLift 187559
  have htrace : WordTrace (prefixWord ++ tailWord_187559) baseStart_187559 baseEnd_187559 := by
    simpa [prefixWord, tailWord_187559, baseEnd_187559] using wordTrace_append hprefix tailTrace_187559
  have hstable : (prefixWord ++ tailWord_187559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187559).length < 2 ^ (prefixWord ++ tailWord_187559).sum := by decide
  have hdescent : baseEnd_187559 < baseStart_187559 := by decide
  rcases family_descends (prefixWord ++ tailWord_187559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187587 : List Nat := [1, 1, 1, 3, 1, 1, 1, 7, 5]
def baseStart_187587 : Nat := 118140960795 + 187587 * 2 ^ 59
def prefixEnd_187587 : Nat := 4983230072969 + 3 ^ 40 * 187587 * 2
def baseEnd_187587 : Nat := 42809909126694577199915

theorem tailTrace_187587 : CollatzResearch.WordTrace tailWord_187587 prefixEnd_187587 42809909126694577199915 := by
  unfold tailWord_187587
  simp only [CollatzResearch.WordTrace]
  refine ⟨6841859971411811154089015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4561239980941207436059343 6841859971411811154089015)
  ·
    refine ⟨10262789957117716731133523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6841859971411811154089015 10262789957117716731133523)
    ·
      refine ⟨15394184935676575096700285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10262789957117716731133523 15394184935676575096700285)
      ·
        refine ⟨5772819350878715661262607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15394184935676575096700285 5772819350878715661262607)
        ·
          refine ⟨8659229026318073491893911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5772819350878715661262607 8659229026318073491893911)
          ·
            refine ⟨12988843539477110237840867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8659229026318073491893911 12988843539477110237840867)
            ·
              refine ⟨19483265309215665356761301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12988843539477110237840867 19483265309215665356761301)
              ·
                refine ⟨456639030684742156799093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 19483265309215665356761301 456639030684742156799093)
                ·
                  refine ⟨42809909126694577199915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 456639030684742156799093 42809909126694577199915)
                  ·
                    rfl

theorem cell21_187587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 5].length) (baseStart_187587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_187587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_187587 prefixEnd_187587 := by exact prefixLift 187587
  have htrace : WordTrace (prefixWord ++ tailWord_187587) baseStart_187587 baseEnd_187587 := by
    simpa [prefixWord, tailWord_187587, baseEnd_187587] using wordTrace_append hprefix tailTrace_187587
  have hstable : (prefixWord ++ tailWord_187587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187587).length < 2 ^ (prefixWord ++ tailWord_187587).sum := by decide
  have hdescent : baseEnd_187587 < baseStart_187587 := by decide
  rcases family_descends (prefixWord ++ tailWord_187587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187635 : List Nat := [1, 1, 1, 2, 2, 6, 2, 2, 4]
def baseStart_187635 : Nat := 118140960795 + 187635 * 2 ^ 59
def prefixEnd_187635 : Nat := 4983230072969 + 3 ^ 40 * 187635 * 2
def baseEnd_187635 : Nat := 42820863380657160399817

theorem tailTrace_187635 : CollatzResearch.WordTrace tailWord_187635 prefixEnd_187635 42820863380657160399817 := by
  unfold tailWord_187635
  simp only [CollatzResearch.WordTrace]
  refine ⟨6843610675237915351836359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4562407116825276901224239 6843610675237915351836359)
  ·
    refine ⟨10265416012856873027754539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6843610675237915351836359 10265416012856873027754539)
    ·
      refine ⟨15398124019285309541631809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10265416012856873027754539 15398124019285309541631809)
      ·
        refine ⟨11548593014463982156223857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15398124019285309541631809 11548593014463982156223857)
        ·
          refine ⟨8661444760847986617167893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11548593014463982156223857 8661444760847986617167893)
          ·
            refine ⟨406005223164749372679745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8661444760847986617167893 406005223164749372679745)
            ·
              refine ⟨304503917373562029509809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406005223164749372679745 304503917373562029509809)
              ·
                refine ⟨228377938030171522132357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304503917373562029509809 228377938030171522132357)
                ·
                  refine ⟨42820863380657160399817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 228377938030171522132357 42820863380657160399817)
                  ·
                    rfl

theorem cell21_187635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 4].length) (baseStart_187635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_187635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_187635 prefixEnd_187635 := by exact prefixLift 187635
  have htrace : WordTrace (prefixWord ++ tailWord_187635) baseStart_187635 baseEnd_187635 := by
    simpa [prefixWord, tailWord_187635, baseEnd_187635] using wordTrace_append hprefix tailTrace_187635
  have hstable : (prefixWord ++ tailWord_187635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187635).length < 2 ^ (prefixWord ++ tailWord_187635).sum := by decide
  have hdescent : baseEnd_187635 < baseStart_187635 := by decide
  rcases family_descends (prefixWord ++ tailWord_187635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187649 : List Nat := [1, 2, 4, 1, 1, 3, 3, 6]
def baseStart_187649 : Nat := 118140960795 + 187649 * 2 ^ 59
def prefixEnd_187649 : Nat := 4983230072969 + 3 ^ 40 * 187649 * 2
def baseEnd_187649 : Nat := 14274686123798749055485

theorem tailTrace_187649 : CollatzResearch.WordTrace tailWord_187649 prefixEnd_187649 14274686123798749055485 := by
  unfold tailWord_187649
  simp only [CollatzResearch.WordTrace]
  refine ⟨6844121297187195742846001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4562747531458130495230667 6844121297187195742846001)
  ·
    refine ⟨5133090972890396807134501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6844121297187195742846001 5133090972890396807134501)
    ·
      refine ⟨962454557416949401337719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5133090972890396807134501 962454557416949401337719)
      ·
        refine ⟨1443681836125424102006579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 962454557416949401337719 1443681836125424102006579)
        ·
          refine ⟨2165522754188136153009869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1443681836125424102006579 2165522754188136153009869)
          ·
            refine ⟨812071032820551057378701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2165522754188136153009869 812071032820551057378701)
            ·
              refine ⟨304526637307706646517013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 812071032820551057378701 304526637307706646517013)
              ·
                refine ⟨14274686123798749055485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 304526637307706646517013 14274686123798749055485)
                ·
                  rfl

theorem cell21_187649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 6].length) (baseStart_187649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_187649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_187649 prefixEnd_187649 := by exact prefixLift 187649
  have htrace : WordTrace (prefixWord ++ tailWord_187649) baseStart_187649 baseEnd_187649 := by
    simpa [prefixWord, tailWord_187649, baseEnd_187649] using wordTrace_append hprefix tailTrace_187649
  have hstable : (prefixWord ++ tailWord_187649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187649).length < 2 ^ (prefixWord ++ tailWord_187649).sum := by decide
  have hdescent : baseEnd_187649 < baseStart_187649 := by decide
  rcases family_descends (prefixWord ++ tailWord_187649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187697 : List Nat := [1, 2, 2, 3, 3, 1, 2, 4, 3]
def baseStart_187697 : Nat := 118140960795 + 187697 * 2 ^ 59
def prefixEnd_187697 : Nat := 4983230072969 + 3 ^ 40 * 187697 * 2
def baseEnd_187697 : Nat := 42835012625358830366357

theorem tailTrace_187697 : CollatzResearch.WordTrace tailWord_187697 prefixEnd_187697 42835012625358830366357 := by
  unfold tailWord_187697
  simp only [CollatzResearch.WordTrace]
  refine ⟨6845872001013299940593345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4563914667342199960395563 6845872001013299940593345)
  ·
    refine ⟨5134404000759974955445009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6845872001013299940593345 5134404000759974955445009)
    ·
      refine ⟨3850803000569981216583757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5134404000759974955445009 3850803000569981216583757)
      ·
        refine ⟨1444051125213742956218909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3850803000569981216583757 1444051125213742956218909)
        ·
          refine ⟨541519171955153608582091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1444051125213742956218909 541519171955153608582091)
          ·
            refine ⟨812278757932730412873137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541519171955153608582091 812278757932730412873137)
            ·
              refine ⟨609209068449547809654853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 812278757932730412873137 609209068449547809654853)
              ·
                refine ⟨114226700334290214310285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 609209068449547809654853 114226700334290214310285)
                ·
                  refine ⟨42835012625358830366357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114226700334290214310285 42835012625358830366357)
                  ·
                    rfl

theorem cell21_187697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4, 3].length) (baseStart_187697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_187697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_187697 prefixEnd_187697 := by exact prefixLift 187697
  have htrace : WordTrace (prefixWord ++ tailWord_187697) baseStart_187697 baseEnd_187697 := by
    simpa [prefixWord, tailWord_187697, baseEnd_187697] using wordTrace_append hprefix tailTrace_187697
  have hstable : (prefixWord ++ tailWord_187697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187697).length < 2 ^ (prefixWord ++ tailWord_187697).sum := by decide
  have hdescent : baseEnd_187697 < baseStart_187697 := by decide
  rcases family_descends (prefixWord ++ tailWord_187697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187756 : List Nat := [2, 2, 1, 1, 5, 1, 3, 1, 5]
def baseStart_187756 : Nat := 118140960795 + 187756 * 2 ^ 59
def prefixEnd_187756 : Nat := 4983230072969 + 3 ^ 40 * 187756 * 2
def baseEnd_187756 : Nat := 42848477229187838882903

theorem tailTrace_187756 : CollatzResearch.WordTrace tailWord_187756 prefixEnd_187756 42848477229187838882903 := by
  unfold tailWord_187756
  simp only [CollatzResearch.WordTrace]
  refine ⟨3424011953899776508495561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4565349271866368677994081 3424011953899776508495561)
  ·
    refine ⟨2568008965424832381371671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3424011953899776508495561 2568008965424832381371671)
    ·
      refine ⟨3852013448137248572057507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2568008965424832381371671 3852013448137248572057507)
      ·
        refine ⟨5778020172205872858086261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3852013448137248572057507 5778020172205872858086261)
        ·
          refine ⟨541689391144300580445587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5778020172205872858086261 541689391144300580445587)
          ·
            refine ⟨812534086716450870668381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541689391144300580445587 812534086716450870668381)
            ·
              refine ⟨304700282518669076500643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 812534086716450870668381 304700282518669076500643)
              ·
                refine ⟨457050423778003614750965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304700282518669076500643 457050423778003614750965)
                ·
                  refine ⟨42848477229187838882903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 457050423778003614750965 42848477229187838882903)
                  ·
                    rfl

theorem cell21_187756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_187756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_187756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_187756 prefixEnd_187756 := by exact prefixLift 187756
  have htrace : WordTrace (prefixWord ++ tailWord_187756) baseStart_187756 baseEnd_187756 := by
    simpa [prefixWord, tailWord_187756, baseEnd_187756] using wordTrace_append hprefix tailTrace_187756
  have hstable : (prefixWord ++ tailWord_187756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187756).length < 2 ^ (prefixWord ++ tailWord_187756).sum := by decide
  have hdescent : baseEnd_187756 < baseStart_187756 := by decide
  rcases family_descends (prefixWord ++ tailWord_187756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187770 : List Nat := [3, 1, 1, 1, 1, 1, 2, 7, 4]
def baseStart_187770 : Nat := 118140960795 + 187770 * 2 ^ 59
def prefixEnd_187770 : Nat := 4983230072969 + 3 ^ 40 * 187770 * 2
def baseEnd_187770 : Nat := 42851672219926925649541

theorem tailTrace_187770 : CollatzResearch.WordTrace tailWord_187770 prefixEnd_187770 42851672219926925649541 := by
  unfold tailWord_187770
  simp only [CollatzResearch.WordTrace]
  refine ⟨1712133632437208352000191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4565689686499222272000509 1712133632437208352000191)
  ·
    refine ⟨2568200448655812528000287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1712133632437208352000191 2568200448655812528000287)
    ·
      refine ⟨3852300672983718792000431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2568200448655812528000287 3852300672983718792000431)
      ·
        refine ⟨5778451009475578188000647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3852300672983718792000431 5778451009475578188000647)
        ·
          refine ⟨8667676514213367282000971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5778451009475578188000647 8667676514213367282000971)
          ·
            refine ⟨13001514771320050923001457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8667676514213367282000971 13001514771320050923001457)
            ·
              refine ⟨9751136078490038192251093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13001514771320050923001457 9751136078490038192251093)
              ·
                refine ⟨228542251839610270130885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 9751136078490038192251093 228542251839610270130885)
                ·
                  refine ⟨42851672219926925649541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 228542251839610270130885 42851672219926925649541)
                  ·
                    rfl

theorem cell21_187770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_187770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_187770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_187770 prefixEnd_187770 := by exact prefixLift 187770
  have htrace : WordTrace (prefixWord ++ tailWord_187770) baseStart_187770 baseEnd_187770 := by
    simpa [prefixWord, tailWord_187770, baseEnd_187770] using wordTrace_append hprefix tailTrace_187770
  have hstable : (prefixWord ++ tailWord_187770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187770).length < 2 ^ (prefixWord ++ tailWord_187770).sum := by decide
  have hdescent : baseEnd_187770 < baseStart_187770 := by decide
  rcases family_descends (prefixWord ++ tailWord_187770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187894 : List Nat := [5, 1, 1, 1, 2, 2, 4, 5]
def baseStart_187894 : Nat := 118140960795 + 187894 * 2 ^ 59
def prefixEnd_187894 : Nat := 4983230072969 + 3 ^ 40 * 187894 * 2
def baseEnd_187894 : Nat := 14293323569776755194207

theorem tailTrace_187894 : CollatzResearch.WordTrace tailWord_187894 prefixEnd_187894 14293323569776755194207 := by
  unfold tailWord_187894
  simp only [CollatzResearch.WordTrace]
  refine ⟨428316073831225161594671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4568704787533068390343157 428316073831225161594671)
  ·
    refine ⟨642474110746837742392007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 428316073831225161594671 642474110746837742392007)
    ·
      refine ⟨963711166120256613588011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 642474110746837742392007 963711166120256613588011)
      ·
        refine ⟨1445566749180384920382017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 963711166120256613588011 1445566749180384920382017)
        ·
          refine ⟨1084175061885288690286513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1445566749180384920382017 1084175061885288690286513)
          ·
            refine ⟨813131296413966517714885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1084175061885288690286513 813131296413966517714885)
            ·
              refine ⟨152462118077618722071541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 813131296413966517714885 152462118077618722071541)
              ·
                refine ⟨14293323569776755194207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152462118077618722071541 14293323569776755194207)
                ·
                  rfl

theorem cell21_187894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_187894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_187894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_187894 prefixEnd_187894 := by exact prefixLift 187894
  have htrace : WordTrace (prefixWord ++ tailWord_187894) baseStart_187894 baseEnd_187894 := by
    simpa [prefixWord, tailWord_187894, baseEnd_187894] using wordTrace_append hprefix tailTrace_187894
  have hstable : (prefixWord ++ tailWord_187894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187894).length < 2 ^ (prefixWord ++ tailWord_187894).sum := by decide
  have hdescent : baseEnd_187894 < baseStart_187894 := by decide
  rcases family_descends (prefixWord ++ tailWord_187894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187939 : List Nat := [1, 1, 1, 4, 5, 1, 1, 3, 4]
def baseStart_187939 : Nat := 118140960795 + 187939 * 2 ^ 59
def prefixEnd_187939 : Nat := 4983230072969 + 3 ^ 40 * 187939 * 2
def baseEnd_187939 : Nat := 42890240322420187332529

theorem tailTrace_187939 : CollatzResearch.WordTrace tailWord_187939 prefixEnd_187939 42890240322420187332529 := by
  unfold tailWord_187939
  simp only [CollatzResearch.WordTrace]
  refine ⟨6854698466136575270902871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4569798977424383513935247 6854698466136575270902871)
  ·
    refine ⟨10282047699204862906354307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6854698466136575270902871 10282047699204862906354307)
    ·
      refine ⟨15423071548807294359531461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10282047699204862906354307 15423071548807294359531461)
      ·
        refine ⟨2891825915401367692412149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15423071548807294359531461 2891825915401367692412149)
        ·
          refine ⟨271108679568878221163639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2891825915401367692412149 271108679568878221163639)
          ·
            refine ⟨406663019353317331745459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271108679568878221163639 406663019353317331745459)
            ·
              refine ⟨609994529029975997618189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406663019353317331745459 609994529029975997618189)
              ·
                refine ⟨228747948386240999106821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 609994529029975997618189 228747948386240999106821)
                ·
                  refine ⟨42890240322420187332529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 228747948386240999106821 42890240322420187332529)
                  ·
                    rfl

theorem cell21_187939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 4].length) (baseStart_187939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_187939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_187939 prefixEnd_187939 := by exact prefixLift 187939
  have htrace : WordTrace (prefixWord ++ tailWord_187939) baseStart_187939 baseEnd_187939 := by
    simpa [prefixWord, tailWord_187939, baseEnd_187939] using wordTrace_append hprefix tailTrace_187939
  have hstable : (prefixWord ++ tailWord_187939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187939).length < 2 ^ (prefixWord ++ tailWord_187939).sum := by decide
  have hdescent : baseEnd_187939 < baseStart_187939 := by decide
  rcases family_descends (prefixWord ++ tailWord_187939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187984 : List Nat := [2, 1, 1, 1, 1, 3, 5, 4, 3]
def baseStart_187984 : Nat := 118140960795 + 187984 * 2 ^ 59
def prefixEnd_187984 : Nat := 4983230072969 + 3 ^ 40 * 187984 * 2
def baseEnd_187984 : Nat := 42900509935510109082437

theorem tailTrace_187984 : CollatzResearch.WordTrace tailWord_187984 prefixEnd_187984 42900509935510109082437 := by
  unfold tailWord_187984
  simp only [CollatzResearch.WordTrace]
  refine ⟨3428169875486773978145503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4570893167315698637527337 3428169875486773978145503)
  ·
    refine ⟨5142254813230160967218255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3428169875486773978145503 5142254813230160967218255)
    ·
      refine ⟨7713382219845241450827383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5142254813230160967218255 7713382219845241450827383)
      ·
        refine ⟨11570073329767862176241075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7713382219845241450827383 11570073329767862176241075)
        ·
          refine ⟨17355109994651793264361613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11570073329767862176241075 17355109994651793264361613)
          ·
            refine ⟨6508166247994422474135605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17355109994651793264361613 6508166247994422474135605)
            ·
              refine ⟨610140585749477106950213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6508166247994422474135605 610140585749477106950213)
              ·
                refine ⟨114401359828026957553165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 610140585749477106950213 114401359828026957553165)
                ·
                  refine ⟨42900509935510109082437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114401359828026957553165 42900509935510109082437)
                  ·
                    rfl

theorem cell21_187984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4, 3].length) (baseStart_187984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_187984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_187984 prefixEnd_187984 := by exact prefixLift 187984
  have htrace : WordTrace (prefixWord ++ tailWord_187984) baseStart_187984 baseEnd_187984 := by
    simpa [prefixWord, tailWord_187984, baseEnd_187984] using wordTrace_append hprefix tailTrace_187984
  have hstable : (prefixWord ++ tailWord_187984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187984).length < 2 ^ (prefixWord ++ tailWord_187984).sum := by decide
  have hdescent : baseEnd_187984 < baseStart_187984 := by decide
  rcases family_descends (prefixWord ++ tailWord_187984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188043 : List Nat := [1, 1, 1, 1, 4, 1, 6, 1, 5]
def baseStart_188043 : Nat := 118140960795 + 188043 * 2 ^ 59
def prefixEnd_188043 : Nat := 4983230072969 + 3 ^ 40 * 188043 * 2
def baseEnd_188043 : Nat := 42913974539339117598983

theorem tailTrace_188043 : CollatzResearch.WordTrace tailWord_188043 prefixEnd_188043 42913974539339117598983 := by
  unfold tailWord_188043
  simp only [CollatzResearch.WordTrace]
  refine ⟨6858491657759801032688783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4572327771839867355125855 6858491657759801032688783)
  ·
    refine ⟨10287737486639701549033175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6858491657759801032688783 10287737486639701549033175)
    ·
      refine ⟨15431606229959552323549763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10287737486639701549033175 15431606229959552323549763)
      ·
        refine ⟨23147409344939328485324645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15431606229959552323549763 23147409344939328485324645)
        ·
          refine ⟨4340139252176124090998371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23147409344939328485324645 4340139252176124090998371)
          ·
            refine ⟨6510208878264186136497557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4340139252176124090998371 6510208878264186136497557)
            ·
              refine ⟨305166041168633725148323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6510208878264186136497557 305166041168633725148323)
              ·
                refine ⟨457749061752950587722485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305166041168633725148323 457749061752950587722485)
                ·
                  refine ⟨42913974539339117598983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 457749061752950587722485 42913974539339117598983)
                  ·
                    rfl

theorem cell21_188043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 5].length) (baseStart_188043 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_188043 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_188043 prefixEnd_188043 := by exact prefixLift 188043
  have htrace : WordTrace (prefixWord ++ tailWord_188043) baseStart_188043 baseEnd_188043 := by
    simpa [prefixWord, tailWord_188043, baseEnd_188043] using wordTrace_append hprefix tailTrace_188043
  have hstable : (prefixWord ++ tailWord_188043).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188043).length < 2 ^ (prefixWord ++ tailWord_188043).sum := by decide
  have hdescent : baseEnd_188043 < baseStart_188043 := by decide
  rcases family_descends (prefixWord ++ tailWord_188043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188063 : List Nat := [1, 1, 2, 7, 1, 2, 2, 5]
def baseStart_188063 : Nat := 118140960795 + 188063 * 2 ^ 59
def prefixEnd_188063 : Nat := 4983230072969 + 3 ^ 40 * 188063 * 2
def baseEnd_188063 : Nat := 14306179603941175755203

theorem tailTrace_188063 : CollatzResearch.WordTrace tailWord_188063 prefixEnd_188063 14306179603941175755203 := by
  unfold tailWord_188063
  simp only [CollatzResearch.WordTrace]
  refine ⟨6859221117687344448416843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4572814078458229632277895 6859221117687344448416843)
  ·
    refine ⟨10288831676531016672625265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6859221117687344448416843 10288831676531016672625265)
    ·
      refine ⟨7716623757398262504468949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10288831676531016672625265 7716623757398262504468949)
      ·
        refine ⟨180858369314021777448491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 7716623757398262504468949 180858369314021777448491)
        ·
          refine ⟨271287553971032666172737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180858369314021777448491 271287553971032666172737)
          ·
            refine ⟨203465665478274499629553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271287553971032666172737 203465665478274499629553)
            ·
              refine ⟨152599249108705874722165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203465665478274499629553 152599249108705874722165)
              ·
                refine ⟨14306179603941175755203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152599249108705874722165 14306179603941175755203)
                ·
                  rfl

theorem cell21_188063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 5].length) (baseStart_188063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_188063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_188063 prefixEnd_188063 := by exact prefixLift 188063
  have htrace : WordTrace (prefixWord ++ tailWord_188063) baseStart_188063 baseEnd_188063 := by
    simpa [prefixWord, tailWord_188063, baseEnd_188063] using wordTrace_append hprefix tailTrace_188063
  have hstable : (prefixWord ++ tailWord_188063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188063).length < 2 ^ (prefixWord ++ tailWord_188063).sum := by decide
  have hdescent : baseEnd_188063 < baseStart_188063 := by decide
  rcases family_descends (prefixWord ++ tailWord_188063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188094 : List Nat := [4, 2, 1, 1, 2, 3, 3, 2, 3]
def baseStart_188094 : Nat := 118140960795 + 188094 * 2 ^ 59
def prefixEnd_188094 : Nat := 4983230072969 + 3 ^ 40 * 188094 * 2
def baseEnd_188094 : Nat := 42925613434174362248879

theorem tailTrace_188094 : CollatzResearch.WordTrace tailWord_188094 prefixEnd_188094 42925613434174362248879 := by
  unfold tailWord_188094
  simp only [CollatzResearch.WordTrace]
  refine ⟨857543972571879592849417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4573567853716691161863557 857543972571879592849417)
  ·
    refine ⟨643157979428909694637063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 857543972571879592849417 643157979428909694637063)
    ·
      refine ⟨964736969143364541955595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 643157979428909694637063 964736969143364541955595)
      ·
        refine ⟨1447105453715046812933393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 964736969143364541955595 1447105453715046812933393)
        ·
          refine ⟨1085329090286285109700045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1447105453715046812933393 1085329090286285109700045)
          ·
            refine ⟨406998408857356916137517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1085329090286285109700045 406998408857356916137517)
            ·
              refine ⟨152624403321508843551569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 406998408857356916137517 152624403321508843551569)
              ·
                refine ⟨114468302491131632663677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152624403321508843551569 114468302491131632663677)
                ·
                  refine ⟨42925613434174362248879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114468302491131632663677 42925613434174362248879)
                  ·
                    rfl

theorem cell21_188094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_188094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_188094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_188094 prefixEnd_188094 := by exact prefixLift 188094
  have htrace : WordTrace (prefixWord ++ tailWord_188094) baseStart_188094 baseEnd_188094 := by
    simpa [prefixWord, tailWord_188094, baseEnd_188094] using wordTrace_append hprefix tailTrace_188094
  have hstable : (prefixWord ++ tailWord_188094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188094).length < 2 ^ (prefixWord ++ tailWord_188094).sum := by decide
  have hdescent : baseEnd_188094 < baseStart_188094 := by decide
  rcases family_descends (prefixWord ++ tailWord_188094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188173 : List Nat := [1, 7, 2, 1, 1, 1, 3, 5]
def baseStart_188173 : Nat := 118140960795 + 188173 * 2 ^ 59
def prefixEnd_188173 : Nat := 4983230072969 + 3 ^ 40 * 188173 * 2
def baseEnd_188173 : Nat := 14314547436829260144017

theorem tailTrace_188173 : CollatzResearch.WordTrace tailWord_188173 prefixEnd_188173 14314547436829260144017 := by
  unfold tailWord_188173
  simp only [CollatzResearch.WordTrace]
  refine ⟨6863233147288833234921173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4575488764859222156614115 6863233147288833234921173)
  ·
    refine ⟨160857026889582028943465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 6863233147288833234921173 160857026889582028943465)
    ·
      refine ⟨120642770167186521707599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160857026889582028943465 120642770167186521707599)
      ·
        refine ⟨180964155250779782561399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120642770167186521707599 180964155250779782561399)
        ·
          refine ⟨271446232876169673842099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180964155250779782561399 271446232876169673842099)
          ·
            refine ⟨407169349314254510763149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271446232876169673842099 407169349314254510763149)
            ·
              refine ⟨152688505992845441536181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 407169349314254510763149 152688505992845441536181)
              ·
                refine ⟨14314547436829260144017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152688505992845441536181 14314547436829260144017)
                ·
                  rfl

theorem cell21_188173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 5].length) (baseStart_188173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_188173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_188173 prefixEnd_188173 := by exact prefixLift 188173
  have htrace : WordTrace (prefixWord ++ tailWord_188173) baseStart_188173 baseEnd_188173 := by
    simpa [prefixWord, tailWord_188173, baseEnd_188173] using wordTrace_append hprefix tailTrace_188173
  have hstable : (prefixWord ++ tailWord_188173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188173).length < 2 ^ (prefixWord ++ tailWord_188173).sum := by decide
  have hdescent : baseEnd_188173 < baseStart_188173 := by decide
  rcases family_descends (prefixWord ++ tailWord_188173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188181 : List Nat := [1, 3, 2, 1, 2, 4, 3, 5]
def baseStart_188181 : Nat := 118140960795 + 188181 * 2 ^ 59
def prefixEnd_188181 : Nat := 4983230072969 + 3 ^ 40 * 188181 * 2
def baseEnd_188181 : Nat := 14315156006493848099567

theorem tailTrace_188181 : CollatzResearch.WordTrace tailWord_188181 prefixEnd_188181 14315156006493848099567 := by
  unfold tailWord_188181
  simp only [CollatzResearch.WordTrace]
  refine ⟨6863524931259850601212397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4575683287506567067474931 6863524931259850601212397)
  ·
    refine ⟨2573821849222443975454649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6863524931259850601212397 2573821849222443975454649)
    ·
      refine ⟨1930366386916832981590987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2573821849222443975454649 1930366386916832981590987)
      ·
        refine ⟨2895549580375249472386481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1930366386916832981590987 2895549580375249472386481)
        ·
          refine ⟨2171662185281437104289861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2895549580375249472386481 2171662185281437104289861)
          ·
            refine ⟨407186659740269457054349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2171662185281437104289861 407186659740269457054349)
            ·
              refine ⟨152694997402601046395381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 407186659740269457054349 152694997402601046395381)
              ·
                refine ⟨14315156006493848099567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152694997402601046395381 14315156006493848099567)
                ·
                  rfl

theorem cell21_188181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 5].length) (baseStart_188181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_188181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_188181 prefixEnd_188181 := by exact prefixLift 188181
  have htrace : WordTrace (prefixWord ++ tailWord_188181) baseStart_188181 baseEnd_188181 := by
    simpa [prefixWord, tailWord_188181, baseEnd_188181] using wordTrace_append hprefix tailTrace_188181
  have hstable : (prefixWord ++ tailWord_188181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188181).length < 2 ^ (prefixWord ++ tailWord_188181).sum := by decide
  have hdescent : baseEnd_188181 < baseStart_188181 := by decide
  rcases family_descends (prefixWord ++ tailWord_188181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188212 : List Nat := [2, 5, 1, 1, 2, 1, 1, 3, 5]
def baseStart_188212 : Nat := 118140960795 + 188212 * 2 ^ 59
def prefixEnd_188212 : Nat := 4983230072969 + 3 ^ 40 * 188212 * 2
def baseEnd_188212 : Nat := 42952542641832379281971

theorem tailTrace_188212 : CollatzResearch.WordTrace tailWord_188212 prefixEnd_188212 42952542641832379281971 := by
  unfold tailWord_188212
  simp only [CollatzResearch.WordTrace]
  refine ⟨3432327797073771447795445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4576437062765028597060593 3432327797073771447795445)
  ·
    refine ⟨321780730975666073230823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3432327797073771447795445 321780730975666073230823)
    ·
      refine ⟨482671096463499109846235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321780730975666073230823 482671096463499109846235)
      ·
        refine ⟨724006644695248664769353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482671096463499109846235 724006644695248664769353)
        ·
          refine ⟨543004983521436498577015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 724006644695248664769353 543004983521436498577015)
          ·
            refine ⟨814507475282154747865523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543004983521436498577015 814507475282154747865523)
            ·
              refine ⟨1221761212923232121798285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 814507475282154747865523 1221761212923232121798285)
              ·
                refine ⟨458160454846212045674357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1221761212923232121798285 458160454846212045674357)
                ·
                  refine ⟨42952542641832379281971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 458160454846212045674357 42952542641832379281971)
                  ·
                    rfl

theorem cell21_188212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_188212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_188212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_188212 prefixEnd_188212 := by exact prefixLift 188212
  have htrace : WordTrace (prefixWord ++ tailWord_188212) baseStart_188212 baseEnd_188212 := by
    simpa [prefixWord, tailWord_188212, baseEnd_188212] using wordTrace_append hprefix tailTrace_188212
  have hstable : (prefixWord ++ tailWord_188212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188212).length < 2 ^ (prefixWord ++ tailWord_188212).sum := by decide
  have hdescent : baseEnd_188212 < baseStart_188212 := by decide
  rcases family_descends (prefixWord ++ tailWord_188212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188316 : List Nat := [2, 2, 3, 3, 1, 10]
def baseStart_188316 : Nat := 118140960795 + 188316 * 2 ^ 59
def prefixEnd_188316 : Nat := 4983230072969 + 3 ^ 40 * 188316 * 2
def baseEnd_188316 : Nat := 1591713957731529983275

theorem tailTrace_188316 : CollatzResearch.WordTrace tailWord_188316 prefixEnd_188316 1591713957731529983275 := by
  unfold tailWord_188316
  simp only [CollatzResearch.WordTrace]
  refine ⟨3434224392885384328688401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4578965857180512438251201 3434224392885384328688401)
  ·
    refine ⟨2575668294664038246516301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3434224392885384328688401 2575668294664038246516301)
    ·
      refine ⟨965875610499014342443613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2575668294664038246516301 965875610499014342443613)
      ·
        refine ⟨362203353937130378416355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 965875610499014342443613 362203353937130378416355)
        ·
          refine ⟨543305030905695567624533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362203353937130378416355 543305030905695567624533)
          ·
            refine ⟨1591713957731529983275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 543305030905695567624533 1591713957731529983275)
            ·
              rfl

theorem cell21_188316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 10].length) (baseStart_188316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_188316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_188316 prefixEnd_188316 := by exact prefixLift 188316
  have htrace : WordTrace (prefixWord ++ tailWord_188316) baseStart_188316 baseEnd_188316 := by
    simpa [prefixWord, tailWord_188316, baseEnd_188316] using wordTrace_append hprefix tailTrace_188316
  have hstable : (prefixWord ++ tailWord_188316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188316).length < 2 ^ (prefixWord ++ tailWord_188316).sum := by decide
  have hdescent : baseEnd_188316 < baseStart_188316 := by decide
  rcases family_descends (prefixWord ++ tailWord_188316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188319 : List Nat := [1, 1, 2, 5, 3, 1, 2, 2, 4]
def baseStart_188319 : Nat := 118140960795 + 188319 * 2 ^ 59
def prefixEnd_188319 : Nat := 4983230072969 + 3 ^ 40 * 188319 * 2
def baseEnd_188319 : Nat := 42976961499623970998419

theorem tailTrace_188319 : CollatzResearch.WordTrace tailWord_188319 prefixEnd_188319 42976961499623970998419 := by
  unfold tailWord_188319
  simp only [CollatzResearch.WordTrace]
  refine ⟨6868558204759900169736011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4579038803173266779824007 6868558204759900169736011)
  ·
    refine ⟨10302837307139850254604017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6868558204759900169736011 10302837307139850254604017)
    ·
      refine ⟨7727127980354887690953013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10302837307139850254604017 7727127980354887690953013)
      ·
        refine ⟨724418248158270721026845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7727127980354887690953013 724418248158270721026845)
        ·
          refine ⟨271656843059351520385067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 724418248158270721026845 271656843059351520385067)
          ·
            refine ⟨407485264589027280577601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271656843059351520385067 407485264589027280577601)
            ·
              refine ⟨305613948441770460433201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 407485264589027280577601 305613948441770460433201)
              ·
                refine ⟨229210461331327845324901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305613948441770460433201 229210461331327845324901)
                ·
                  refine ⟨42976961499623970998419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 229210461331327845324901 42976961499623970998419)
                  ·
                    rfl

theorem cell21_188319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 4].length) (baseStart_188319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_188319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_188319 prefixEnd_188319 := by exact prefixLift 188319
  have htrace : WordTrace (prefixWord ++ tailWord_188319) baseStart_188319 baseEnd_188319 := by
    simpa [prefixWord, tailWord_188319, baseEnd_188319] using wordTrace_append hprefix tailTrace_188319
  have hstable : (prefixWord ++ tailWord_188319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188319).length < 2 ^ (prefixWord ++ tailWord_188319).sum := by decide
  have hdescent : baseEnd_188319 < baseStart_188319 := by decide
  rcases family_descends (prefixWord ++ tailWord_188319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188364 : List Nat := [2, 2, 1, 4, 1, 2, 1, 5, 3]
def baseStart_188364 : Nat := 118140960795 + 188364 * 2 ^ 59
def prefixEnd_188364 : Nat := 4983230072969 + 3 ^ 40 * 188364 * 2
def baseEnd_188364 : Nat := 42987231112713892748327

theorem tailTrace_188364 : CollatzResearch.WordTrace tailWord_188364 prefixEnd_188364 42987231112713892748327 := by
  unfold tailWord_188364
  simp only [CollatzResearch.WordTrace]
  refine ⟨3435099744798436427562073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4580132993064581903416097 3435099744798436427562073)
  ·
    refine ⟨2576324808598827320671555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3435099744798436427562073 2576324808598827320671555)
    ·
      refine ⟨3864487212898240981007333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2576324808598827320671555 3864487212898240981007333)
      ·
        refine ⟨724591352418420183938875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3864487212898240981007333 724591352418420183938875)
        ·
          refine ⟨1086887028627630275908313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 724591352418420183938875 1086887028627630275908313)
          ·
            refine ⟨815165271470722706931235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1086887028627630275908313 815165271470722706931235)
            ·
              refine ⟨1222747907206084060396853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 815165271470722706931235 1222747907206084060396853)
              ·
                refine ⟨114632616300570380662205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1222747907206084060396853 114632616300570380662205)
                ·
                  refine ⟨42987231112713892748327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114632616300570380662205 42987231112713892748327)
                  ·
                    rfl

theorem cell21_188364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5, 3].length) (baseStart_188364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_188364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_188364 prefixEnd_188364 := by exact prefixLift 188364
  have htrace : WordTrace (prefixWord ++ tailWord_188364) baseStart_188364 baseEnd_188364 := by
    simpa [prefixWord, tailWord_188364, baseEnd_188364] using wordTrace_append hprefix tailTrace_188364
  have hstable : (prefixWord ++ tailWord_188364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188364).length < 2 ^ (prefixWord ++ tailWord_188364).sum := by decide
  have hdescent : baseEnd_188364 < baseStart_188364 := by decide
  rcases family_descends (prefixWord ++ tailWord_188364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188375 : List Nat := [1, 1, 3, 2, 1, 1, 12]
def baseStart_188375 : Nat := 118140960795 + 188375 * 2 ^ 59
def prefixEnd_188375 : Nat := 4983230072969 + 3 ^ 40 * 188375 * 2
def baseEnd_188375 : Nat := 4776637940286702007219

theorem tailTrace_188375 : CollatzResearch.WordTrace tailWord_188375 prefixEnd_188375 4776637940286702007219 := by
  unfold tailWord_188375
  simp only [CollatzResearch.WordTrace]
  refine ⟨6870600692557021733774579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4580400461704681155849719 6870600692557021733774579)
  ·
    refine ⟨10305901038835532600661869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6870600692557021733774579 10305901038835532600661869)
    ·
      refine ⟨3864712889563324725248201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10305901038835532600661869 3864712889563324725248201)
      ·
        refine ⟨2898534667172493543936151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3864712889563324725248201 2898534667172493543936151)
        ·
          refine ⟨4347802000758740315904227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2898534667172493543936151 4347802000758740315904227)
          ·
            refine ⟨6521703001138110473856341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4347802000758740315904227 6521703001138110473856341)
            ·
              refine ⟨4776637940286702007219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 6521703001138110473856341 4776637940286702007219)
              ·
                rfl

theorem cell21_188375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 12].length) (baseStart_188375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_188375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_188375 prefixEnd_188375 := by exact prefixLift 188375
  have htrace : WordTrace (prefixWord ++ tailWord_188375) baseStart_188375 baseEnd_188375 := by
    simpa [prefixWord, tailWord_188375, baseEnd_188375] using wordTrace_append hprefix tailTrace_188375
  have hstable : (prefixWord ++ tailWord_188375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188375).length < 2 ^ (prefixWord ++ tailWord_188375).sum := by decide
  have hdescent : baseEnd_188375 < baseStart_188375 := by decide
  rcases family_descends (prefixWord ++ tailWord_188375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188378 : List Nat := [3, 1, 1, 2, 5, 1, 1, 1, 6]
def baseStart_188378 : Nat := 118140960795 + 188378 * 2 ^ 59
def prefixEnd_188378 : Nat := 4983230072969 + 3 ^ 40 * 188378 * 2
def baseEnd_188378 : Nat := 42990426103452979514965

theorem tailTrace_188378 : CollatzResearch.WordTrace tailWord_188378 prefixEnd_188378 42990426103452979514965 := by
  unfold tailWord_188378
  simp only [CollatzResearch.WordTrace]
  refine ⟨1717677527886538311533447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4580473407697435497422525 1717677527886538311533447)
  ·
    refine ⟨2576516291829807467300171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1717677527886538311533447 2576516291829807467300171)
    ·
      refine ⟨3864774437744711200950257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2576516291829807467300171 3864774437744711200950257)
      ·
        refine ⟨2898580828308533400712693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3864774437744711200950257 2898580828308533400712693)
        ·
          refine ⟨271741952653925006316815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2898580828308533400712693 271741952653925006316815)
          ·
            refine ⟨407612928980887509475223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271741952653925006316815 407612928980887509475223)
            ·
              refine ⟨611419393471331264212835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 407612928980887509475223 611419393471331264212835)
              ·
                refine ⟨917129090206996896319253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 611419393471331264212835 917129090206996896319253)
                ·
                  refine ⟨42990426103452979514965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 917129090206996896319253 42990426103452979514965)
                  ·
                    rfl

theorem cell21_188378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_188378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_188378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_188378 prefixEnd_188378 := by exact prefixLift 188378
  have htrace : WordTrace (prefixWord ++ tailWord_188378) baseStart_188378 baseEnd_188378 := by
    simpa [prefixWord, tailWord_188378, baseEnd_188378] using wordTrace_append hprefix tailTrace_188378
  have hstable : (prefixWord ++ tailWord_188378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188378).length < 2 ^ (prefixWord ++ tailWord_188378).sum := by decide
  have hdescent : baseEnd_188378 < baseStart_188378 := by decide
  rcases family_descends (prefixWord ++ tailWord_188378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188409 : List Nat := [1, 2, 1, 3, 1, 6, 2, 5]
def baseStart_188409 : Nat := 118140960795 + 188409 * 2 ^ 59
def prefixEnd_188409 : Nat := 4983230072969 + 3 ^ 40 * 188409 * 2
def baseEnd_188409 : Nat := 14332500241934604832745

theorem tailTrace_188409 : CollatzResearch.WordTrace tailWord_188409 prefixEnd_188409 14332500241934604832745 := by
  unfold tailWord_188409
  simp only [CollatzResearch.WordTrace]
  refine ⟨6871840774433845540512281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4581227182955897027008187 6871840774433845540512281)
  ·
    refine ⟨5153880580825384155384211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6871840774433845540512281 5153880580825384155384211)
    ·
      refine ⟨7730820871238076233076317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5153880580825384155384211 7730820871238076233076317)
      ·
        refine ⟨2899057826714278587403619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7730820871238076233076317 2899057826714278587403619)
        ·
          refine ⟨4348586740071417881105429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2899057826714278587403619 4348586740071417881105429)
          ·
            refine ⟨203840003440847713176817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4348586740071417881105429 203840003440847713176817)
            ·
              refine ⟨152880002580635784882613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203840003440847713176817 152880002580635784882613)
              ·
                refine ⟨14332500241934604832745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152880002580635784882613 14332500241934604832745)
                ·
                  rfl

theorem cell21_188409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 5].length) (baseStart_188409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_188409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_188409 prefixEnd_188409 := by exact prefixLift 188409
  have htrace : WordTrace (prefixWord ++ tailWord_188409) baseStart_188409 baseEnd_188409 := by
    simpa [prefixWord, tailWord_188409, baseEnd_188409] using wordTrace_append hprefix tailTrace_188409
  have hstable : (prefixWord ++ tailWord_188409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188409).length < 2 ^ (prefixWord ++ tailWord_188409).sum := by decide
  have hdescent : baseEnd_188409 < baseStart_188409 := by decide
  rcases family_descends (prefixWord ++ tailWord_188409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188502 : List Nat := [5, 2, 2, 1, 1, 1, 3, 6]
def baseStart_188502 : Nat := 118140960795 + 188502 * 2 ^ 59
def prefixEnd_188502 : Nat := 4983230072969 + 3 ^ 40 * 188502 * 2
def baseEnd_188502 : Nat := 14339574864285439816015

theorem tailTrace_188502 : CollatzResearch.WordTrace tailWord_188502 prefixEnd_188502 14339574864285439816015 := by
  unfold tailWord_188502
  simp only [CollatzResearch.WordTrace]
  refine ⟨429702047693557651477985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4583488508731281615765173 429702047693557651477985)
  ·
    refine ⟨322276535770168238608489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 429702047693557651477985 322276535770168238608489)
    ·
      refine ⟨241707401827626178956367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322276535770168238608489 241707401827626178956367)
      ·
        refine ⟨362561102741439268434551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241707401827626178956367 362561102741439268434551)
        ·
          refine ⟨543841654112158902651827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362561102741439268434551 543841654112158902651827)
          ·
            refine ⟨815762481168238353977741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543841654112158902651827 815762481168238353977741)
            ·
              refine ⟨305910930438089382741653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 815762481168238353977741 305910930438089382741653)
              ·
                refine ⟨14339574864285439816015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 305910930438089382741653 14339574864285439816015)
                ·
                  rfl

theorem cell21_188502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_188502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_188502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_188502 prefixEnd_188502 := by exact prefixLift 188502
  have htrace : WordTrace (prefixWord ++ tailWord_188502) baseStart_188502 baseEnd_188502 := by
    simpa [prefixWord, tailWord_188502, baseEnd_188502] using wordTrace_append hprefix tailTrace_188502
  have hstable : (prefixWord ++ tailWord_188502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188502).length < 2 ^ (prefixWord ++ tailWord_188502).sum := by decide
  have hdescent : baseEnd_188502 < baseStart_188502 := by decide
  rcases family_descends (prefixWord ++ tailWord_188502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188575 : List Nat := [1, 1, 2, 6, 1, 1, 2, 2, 5]
def baseStart_188575 : Nat := 118140960795 + 188575 * 2 ^ 59
def prefixEnd_188575 : Nat := 4983230072969 + 3 ^ 40 * 188575 * 2
def baseEnd_188575 : Nat := 43035384187424414731229

theorem tailTrace_188575 : CollatzResearch.WordTrace tailWord_188575 prefixEnd_188575 43035384187424414731229 := by
  unfold tailWord_188575
  simp only [CollatzResearch.WordTrace]
  refine ⟨6877895291832455891055179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4585263527888303927370119 6877895291832455891055179)
  ·
    refine ⟨10316842937748683836582769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6877895291832455891055179 10316842937748683836582769)
    ·
      refine ⟨7737632203311512877437077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10316842937748683836582769 7737632203311512877437077)
      ·
        refine ⟨362701509530227166129863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7737632203311512877437077 362701509530227166129863)
        ·
          refine ⟨544052264295340749194795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362701509530227166129863 544052264295340749194795)
          ·
            refine ⟨816078396443011123792193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544052264295340749194795 816078396443011123792193)
            ·
              refine ⟨612058797332258342844145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 816078396443011123792193 612058797332258342844145)
              ·
                refine ⟨459044097999193757133109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 612058797332258342844145 459044097999193757133109)
                ·
                  refine ⟨43035384187424414731229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 459044097999193757133109 43035384187424414731229)
                  ·
                    rfl

theorem cell21_188575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 5].length) (baseStart_188575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_188575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_188575 prefixEnd_188575 := by exact prefixLift 188575
  have htrace : WordTrace (prefixWord ++ tailWord_188575) baseStart_188575 baseEnd_188575 := by
    simpa [prefixWord, tailWord_188575, baseEnd_188575] using wordTrace_append hprefix tailTrace_188575
  have hstable : (prefixWord ++ tailWord_188575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188575).length < 2 ^ (prefixWord ++ tailWord_188575).sum := by decide
  have hdescent : baseEnd_188575 < baseStart_188575 := by decide
  rcases family_descends (prefixWord ++ tailWord_188575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188578 : List Nat := [3, 3, 1, 3, 1, 3, 2, 5]
def baseStart_188578 : Nat := 118140960795 + 188578 * 2 ^ 59
def prefixEnd_188578 : Nat := 4983230072969 + 3 ^ 40 * 188578 * 2
def baseEnd_188578 : Nat := 14345356276099025393741

theorem tailTrace_188578 : CollatzResearch.WordTrace tailWord_188578 prefixEnd_188578 14345356276099025393741 := by
  unfold tailWord_188578
  simp only [CollatzResearch.WordTrace]
  refine ⟨1719501177705396850853597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4585336473881058268942925 1719501177705396850853597)
  ·
    refine ⟨644812941639523819070099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1719501177705396850853597 644812941639523819070099)
    ·
      refine ⟨967219412459285728605149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 644812941639523819070099 967219412459285728605149)
      ·
        refine ⟨362707279672232148226931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 967219412459285728605149 362707279672232148226931)
        ·
          refine ⟨544060919508348222340397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362707279672232148226931 544060919508348222340397)
          ·
            refine ⟨204022844815630583377649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 544060919508348222340397 204022844815630583377649)
            ·
              refine ⟨153017133611722937533237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204022844815630583377649 153017133611722937533237)
              ·
                refine ⟨14345356276099025393741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 153017133611722937533237 14345356276099025393741)
                ·
                  rfl

theorem cell21_188578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 5].length) (baseStart_188578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_188578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_188578 prefixEnd_188578 := by exact prefixLift 188578
  have htrace : WordTrace (prefixWord ++ tailWord_188578) baseStart_188578 baseEnd_188578 := by
    simpa [prefixWord, tailWord_188578, baseEnd_188578] using wordTrace_append hprefix tailTrace_188578
  have hstable : (prefixWord ++ tailWord_188578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188578).length < 2 ^ (prefixWord ++ tailWord_188578).sum := by decide
  have hdescent : baseEnd_188578 < baseStart_188578 := by decide
  rcases family_descends (prefixWord ++ tailWord_188578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188609 : List Nat := [1, 2, 6, 1, 2, 2, 1, 1, 5]
def baseStart_188609 : Nat := 118140960795 + 188609 * 2 ^ 59
def prefixEnd_188609 : Nat := 4983230072969 + 3 ^ 40 * 188609 * 2
def baseEnd_188609 : Nat := 43043143450647911164493

theorem tailTrace_188609 : CollatzResearch.WordTrace tailWord_188609 prefixEnd_188609 43043143450647911164493 := by
  unfold tailWord_188609
  simp only [CollatzResearch.WordTrace]
  refine ⟨6879135373709279697792881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4586090249139519798528587 6879135373709279697792881)
  ·
    refine ⟨5159351530281959773344661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6879135373709279697792881 5159351530281959773344661)
    ·
      refine ⟨241844602981966864375531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5159351530281959773344661 241844602981966864375531)
      ·
        refine ⟨362766904472950296563297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241844602981966864375531 362766904472950296563297)
        ·
          refine ⟨272075178354712722422473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362766904472950296563297 272075178354712722422473)
          ·
            refine ⟨204056383766034541816855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272075178354712722422473 204056383766034541816855)
            ·
              refine ⟨306084575649051812725283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204056383766034541816855 306084575649051812725283)
              ·
                refine ⟨459126863473577719087925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306084575649051812725283 459126863473577719087925)
                ·
                  refine ⟨43043143450647911164493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 459126863473577719087925 43043143450647911164493)
                  ·
                    rfl

theorem cell21_188609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 5].length) (baseStart_188609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_188609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_188609 prefixEnd_188609 := by exact prefixLift 188609
  have htrace : WordTrace (prefixWord ++ tailWord_188609) baseStart_188609 baseEnd_188609 := by
    simpa [prefixWord, tailWord_188609, baseEnd_188609] using wordTrace_append hprefix tailTrace_188609
  have hstable : (prefixWord ++ tailWord_188609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188609).length < 2 ^ (prefixWord ++ tailWord_188609).sum := by decide
  have hdescent : baseEnd_188609 < baseStart_188609 := by decide
  rcases family_descends (prefixWord ++ tailWord_188609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188634 : List Nat := [3, 1, 1, 2, 2, 1, 2, 4, 5]
def baseStart_188634 : Nat := 118140960795 + 188634 * 2 ^ 59
def prefixEnd_188634 : Nat := 4983230072969 + 3 ^ 40 * 188634 * 2
def baseEnd_188634 : Nat := 43048848791253423247775

theorem tailTrace_188634 : CollatzResearch.WordTrace tailWord_188634 prefixEnd_188634 43048848791253423247775 := by
  unfold tailWord_188634
  simp only [CollatzResearch.WordTrace]
  refine ⟨1720011799654677241863239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4586698132412472644968637 1720011799654677241863239)
  ·
    refine ⟨2580017699482015862794859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1720011799654677241863239 2580017699482015862794859)
    ·
      refine ⟨3870026549223023794192289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2580017699482015862794859 3870026549223023794192289)
      ·
        refine ⟨2902519911917267845644217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3870026549223023794192289 2902519911917267845644217)
        ·
          refine ⟨2176889933937950884233163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2902519911917267845644217 2176889933937950884233163)
          ·
            refine ⟨3265334900906926326349745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2176889933937950884233163 3265334900906926326349745)
            ·
              refine ⟨2449001175680194744762309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3265334900906926326349745 2449001175680194744762309)
              ·
                refine ⟨459187720440036514642933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2449001175680194744762309 459187720440036514642933)
                ·
                  refine ⟨43048848791253423247775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 459187720440036514642933 43048848791253423247775)
                  ·
                    rfl

theorem cell21_188634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_188634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_188634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_188634 prefixEnd_188634 := by exact prefixLift 188634
  have htrace : WordTrace (prefixWord ++ tailWord_188634) baseStart_188634 baseEnd_188634 := by
    simpa [prefixWord, tailWord_188634, baseEnd_188634] using wordTrace_append hprefix tailTrace_188634
  have hstable : (prefixWord ++ tailWord_188634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188634).length < 2 ^ (prefixWord ++ tailWord_188634).sum := by decide
  have hdescent : baseEnd_188634 < baseStart_188634 := by decide
  rcases family_descends (prefixWord ++ tailWord_188634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188651 : List Nat := [1, 1, 1, 1, 2, 5, 2, 5, 3]
def baseStart_188651 : Nat := 118140960795 + 188651 * 2 ^ 59
def prefixEnd_188651 : Nat := 4983230072969 + 3 ^ 40 * 188651 * 2
def baseEnd_188651 : Nat := 43052728422865171464407

theorem tailTrace_188651 : CollatzResearch.WordTrace tailWord_188651 prefixEnd_188651 43052728422865171464407 := by
  unfold tailWord_188651
  simp only [CollatzResearch.WordTrace]
  refine ⟨6880667239557120870821807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4587111493038080580547871 6880667239557120870821807)
  ·
    refine ⟨10321000859335681306232711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6880667239557120870821807 10321000859335681306232711)
    ·
      refine ⟨15481501289003521959349067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10321000859335681306232711 15481501289003521959349067)
      ·
        refine ⟨23222251933505282939023601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15481501289003521959349067 23222251933505282939023601)
        ·
          refine ⟨17416688950128962204267701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23222251933505282939023601 17416688950128962204267701)
          ·
            refine ⟨1632814589074590206650097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17416688950128962204267701 1632814589074590206650097)
            ·
              refine ⟨1224610941805942654987573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1632814589074590206650097 1224610941805942654987573)
              ·
                refine ⟨114807275794307123905085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1224610941805942654987573 114807275794307123905085)
                ·
                  refine ⟨43052728422865171464407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114807275794307123905085 43052728422865171464407)
                  ·
                    rfl

theorem cell21_188651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5, 3].length) (baseStart_188651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_188651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_188651 prefixEnd_188651 := by exact prefixLift 188651
  have htrace : WordTrace (prefixWord ++ tailWord_188651) baseStart_188651 baseEnd_188651 := by
    simpa [prefixWord, tailWord_188651, baseEnd_188651] using wordTrace_append hprefix tailTrace_188651
  have hstable : (prefixWord ++ tailWord_188651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188651).length < 2 ^ (prefixWord ++ tailWord_188651).sum := by decide
  have hdescent : baseEnd_188651 < baseStart_188651 := by decide
  rcases family_descends (prefixWord ++ tailWord_188651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188668 : List Nat := [2, 2, 2, 1, 4, 2, 1, 4, 3]
def baseStart_188668 : Nat := 118140960795 + 188668 * 2 ^ 59
def prefixEnd_188668 : Nat := 4983230072969 + 3 ^ 40 * 188668 * 2
def baseEnd_188668 : Nat := 43056608054476919681039

theorem tailTrace_188668 : CollatzResearch.WordTrace tailWord_188668 prefixEnd_188668 43056608054476919681039 := by
  unfold tailWord_188668
  simp only [CollatzResearch.WordTrace]
  refine ⟨3440643640247766387095329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4587524853663688516127105 3440643640247766387095329)
  ·
    refine ⟨2580482730185824790321497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3440643640247766387095329 2580482730185824790321497)
    ·
      refine ⟨1935362047639368592741123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2580482730185824790321497 1935362047639368592741123)
      ·
        refine ⟨2903043071459052889111685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1935362047639368592741123 2903043071459052889111685)
        ·
          refine ⟨544320575898572416708441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2903043071459052889111685 544320575898572416708441)
          ·
            refine ⟨408240431923929312531331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 544320575898572416708441 408240431923929312531331)
            ·
              refine ⟨612360647885893968796997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408240431923929312531331 612360647885893968796997)
              ·
                refine ⟨114817621478605119149437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 612360647885893968796997 114817621478605119149437)
                ·
                  refine ⟨43056608054476919681039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114817621478605119149437 43056608054476919681039)
                  ·
                    rfl

theorem cell21_188668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4, 3].length) (baseStart_188668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_188668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_188668 prefixEnd_188668 := by exact prefixLift 188668
  have htrace : WordTrace (prefixWord ++ tailWord_188668) baseStart_188668 baseEnd_188668 := by
    simpa [prefixWord, tailWord_188668, baseEnd_188668] using wordTrace_append hprefix tailTrace_188668
  have hstable : (prefixWord ++ tailWord_188668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188668).length < 2 ^ (prefixWord ++ tailWord_188668).sum := by decide
  have hdescent : baseEnd_188668 < baseStart_188668 := by decide
  rcases family_descends (prefixWord ++ tailWord_188668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188696 : List Nat := [2, 1, 2, 3, 1, 2, 5, 5]
def baseStart_188696 : Nat := 118140960795 + 188696 * 2 ^ 59
def prefixEnd_188696 : Nat := 4983230072969 + 3 ^ 40 * 188696 * 2
def baseEnd_188696 : Nat := 14354332678651697738105

theorem tailTrace_188696 : CollatzResearch.WordTrace tailWord_188696 prefixEnd_188696 14354332678651697738105 := by
  unfold tailWord_188696
  simp only [CollatzResearch.WordTrace]
  refine ⟨3441154262197046778104971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4588205682929395704139961 3441154262197046778104971)
  ·
    refine ⟨5161731393295570167157457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3441154262197046778104971 5161731393295570167157457)
    ·
      refine ⟨3871298544971677625368093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5161731393295570167157457 3871298544971677625368093)
      ·
        refine ⟨1451736954364379109513035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3871298544971677625368093 1451736954364379109513035)
        ·
          refine ⟨2177605431546568664269553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1451736954364379109513035 2177605431546568664269553)
          ·
            refine ⟨1633204073659926498202165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2177605431546568664269553 1633204073659926498202165)
            ·
              refine ⟨153112881905618109206453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1633204073659926498202165 153112881905618109206453)
              ·
                refine ⟨14354332678651697738105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 153112881905618109206453 14354332678651697738105)
                ·
                  rfl

theorem cell21_188696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 5].length) (baseStart_188696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_188696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_188696 prefixEnd_188696 := by exact prefixLift 188696
  have htrace : WordTrace (prefixWord ++ tailWord_188696) baseStart_188696 baseEnd_188696 := by
    simpa [prefixWord, tailWord_188696, baseEnd_188696] using wordTrace_append hprefix tailTrace_188696
  have hstable : (prefixWord ++ tailWord_188696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188696).length < 2 ^ (prefixWord ++ tailWord_188696).sum := by decide
  have hdescent : baseEnd_188696 < baseStart_188696 := by decide
  rcases family_descends (prefixWord ++ tailWord_188696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188702 : List Nat := [4, 3, 2, 1, 1, 2, 2, 3, 3]
def baseStart_188702 : Nat := 118140960795 + 188702 * 2 ^ 59
def prefixEnd_188702 : Nat := 4983230072969 + 3 ^ 40 * 188702 * 2
def baseEnd_188702 : Nat := 43064367317700416114303

theorem tailTrace_188702 : CollatzResearch.WordTrace tailWord_188702 prefixEnd_188702 43064367317700416114303 := by
  unfold tailWord_188702
  simp only [CollatzResearch.WordTrace]
  refine ⟨860315920296544572616045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4588351574914904387285573 860315920296544572616045)
  ·
    refine ⟨322618470111204214731017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 860315920296544572616045 322618470111204214731017)
    ·
      refine ⟨241963852583403161048263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322618470111204214731017 241963852583403161048263)
      ·
        refine ⟨362945778875104741572395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241963852583403161048263 362945778875104741572395)
        ·
          refine ⟨544418668312657112358593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362945778875104741572395 544418668312657112358593)
          ·
            refine ⟨408314001234492834268945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 544418668312657112358593 408314001234492834268945)
            ·
              refine ⟨306235500925869625701709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 408314001234492834268945 306235500925869625701709)
              ·
                refine ⟨114838312847201109638141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306235500925869625701709 114838312847201109638141)
                ·
                  refine ⟨43064367317700416114303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114838312847201109638141 43064367317700416114303)
                  ·
                    rfl

theorem cell21_188702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_188702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_188702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_188702 prefixEnd_188702 := by exact prefixLift 188702
  have htrace : WordTrace (prefixWord ++ tailWord_188702) baseStart_188702 baseEnd_188702 := by
    simpa [prefixWord, tailWord_188702, baseEnd_188702] using wordTrace_append hprefix tailTrace_188702
  have hstable : (prefixWord ++ tailWord_188702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188702).length < 2 ^ (prefixWord ++ tailWord_188702).sum := by decide
  have hdescent : baseEnd_188702 < baseStart_188702 := by decide
  rcases family_descends (prefixWord ++ tailWord_188702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188834 : List Nat := [3, 3, 1, 2, 1, 1, 4, 2, 4]
def baseStart_188834 : Nat := 118140960795 + 188834 * 2 ^ 59
def prefixEnd_188834 : Nat := 4983230072969 + 3 ^ 40 * 188834 * 2
def baseEnd_188834 : Nat := 43094491516097519914033

theorem tailTrace_188834 : CollatzResearch.WordTrace tailWord_188834 prefixEnd_188834 43094491516097519914033 := by
  unfold tailWord_188834
  simp only [CollatzResearch.WordTrace]
  refine ⟨1721835449473535781183389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4591561198596095416489037 1721835449473535781183389)
  ·
    refine ⟨645688293552575917943771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1721835449473535781183389 645688293552575917943771)
    ·
      refine ⟨968532440328863876915657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 645688293552575917943771 968532440328863876915657)
      ·
        refine ⟨726399330246647907686743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 968532440328863876915657 726399330246647907686743)
        ·
          refine ⟨1089598995369971861530115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726399330246647907686743 1089598995369971861530115)
          ·
            refine ⟨1634398493054957792295173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1089598995369971861530115 1634398493054957792295173)
            ·
              refine ⟨306449717447804586055345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1634398493054957792295173 306449717447804586055345)
              ·
                refine ⟨229837288085853439541509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 306449717447804586055345 229837288085853439541509)
                ·
                  refine ⟨43094491516097519914033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 229837288085853439541509 43094491516097519914033)
                  ·
                    rfl

theorem cell21_188834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_188834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_188834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_188834 prefixEnd_188834 := by exact prefixLift 188834
  have htrace : WordTrace (prefixWord ++ tailWord_188834) baseStart_188834 baseEnd_188834 := by
    simpa [prefixWord, tailWord_188834, baseEnd_188834] using wordTrace_append hprefix tailTrace_188834
  have hstable : (prefixWord ++ tailWord_188834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188834).length < 2 ^ (prefixWord ++ tailWord_188834).sum := by decide
  have hdescent : baseEnd_188834 < baseStart_188834 := by decide
  rcases family_descends (prefixWord ++ tailWord_188834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188862 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 7]
def baseStart_188862 : Nat := 118140960795 + 188862 * 2 ^ 59
def prefixEnd_188862 : Nat := 4983230072969 + 3 ^ 40 * 188862 * 2
def baseEnd_188862 : Nat := 43100881497575693447309

theorem tailTrace_188862 : CollatzResearch.WordTrace tailWord_188862 prefixEnd_188862 43100881497575693447309 := by
  unfold tailWord_188862
  simp only [CollatzResearch.WordTrace]
  refine ⟨861045380224087988344105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4592242027861802604501893 861045380224087988344105)
  ·
    refine ⟨645784035168065991258079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 861045380224087988344105 645784035168065991258079)
    ·
      refine ⟨968676052752098986887119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 645784035168065991258079 968676052752098986887119)
      ·
        refine ⟨1453014079128148480330679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 968676052752098986887119 1453014079128148480330679)
        ·
          refine ⟨2179521118692222720496019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1453014079128148480330679 2179521118692222720496019)
          ·
            refine ⟨3269281678038334080744029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2179521118692222720496019 3269281678038334080744029)
            ·
              refine ⟨1225980629264375280279011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3269281678038334080744029 1225980629264375280279011)
              ·
                refine ⟨1838970943896562920418517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225980629264375280279011 1838970943896562920418517)
                ·
                  refine ⟨43100881497575693447309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1838970943896562920418517 43100881497575693447309)
                  ·
                    rfl

theorem cell21_188862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_188862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_188862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_188862 prefixEnd_188862 := by exact prefixLift 188862
  have htrace : WordTrace (prefixWord ++ tailWord_188862) baseStart_188862 baseEnd_188862 := by
    simpa [prefixWord, tailWord_188862, baseEnd_188862] using wordTrace_append hprefix tailTrace_188862
  have hstable : (prefixWord ++ tailWord_188862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188862).length < 2 ^ (prefixWord ++ tailWord_188862).sum := by decide
  have hdescent : baseEnd_188862 < baseStart_188862 := by decide
  rcases family_descends (prefixWord ++ tailWord_188862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188893 : List Nat := [1, 4, 3, 1, 1, 1, 3, 1, 6]
def baseStart_188893 : Nat := 118140960795 + 188893 * 2 ^ 59
def prefixEnd_188893 : Nat := 4983230072969 + 3 ^ 40 * 188893 * 2
def baseEnd_188893 : Nat := 43107956119926528430579

theorem tailTrace_188893 : CollatzResearch.WordTrace tailWord_188893 prefixEnd_188893 43107956119926528430579 := by
  unfold tailWord_188893
  simp only [CollatzResearch.WordTrace]
  refine ⟨6889493704680396201131333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4592995803120264134087555 6889493704680396201131333)
  ·
    refine ⟨1291780069627574287712125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6889493704680396201131333 1291780069627574287712125)
    ·
      refine ⟨484417526110340357892047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1291780069627574287712125 484417526110340357892047)
      ·
        refine ⟨726626289165510536838071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484417526110340357892047 726626289165510536838071)
        ·
          refine ⟨1089939433748265805257107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726626289165510536838071 1089939433748265805257107)
          ·
            refine ⟨1634909150622398707885661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1089939433748265805257107 1634909150622398707885661)
            ·
              refine ⟨613090931483399515457123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1634909150622398707885661 613090931483399515457123)
              ·
                refine ⟨919636397225099273185685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 613090931483399515457123 919636397225099273185685)
                ·
                  refine ⟨43107956119926528430579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 919636397225099273185685 43107956119926528430579)
                  ·
                    rfl

theorem cell21_188893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_188893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_188893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_188893 prefixEnd_188893 := by exact prefixLift 188893
  have htrace : WordTrace (prefixWord ++ tailWord_188893) baseStart_188893 baseEnd_188893 := by
    simpa [prefixWord, tailWord_188893, baseEnd_188893] using wordTrace_append hprefix tailTrace_188893
  have hstable : (prefixWord ++ tailWord_188893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188893).length < 2 ^ (prefixWord ++ tailWord_188893).sum := by decide
  have hdescent : baseEnd_188893 < baseStart_188893 := by decide
  rcases family_descends (prefixWord ++ tailWord_188893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188930 : List Nat := [3, 4, 1, 2, 2, 2, 1, 3, 3]
def baseStart_188930 : Nat := 118140960795 + 188930 * 2 ^ 59
def prefixEnd_188930 : Nat := 4983230072969 + 3 ^ 40 * 188930 * 2
def baseEnd_188930 : Nat := 43116400024022686313837

theorem tailTrace_188930 : CollatzResearch.WordTrace tailWord_188930 prefixEnd_188930 43116400024022686313837 := by
  unfold tailWord_188930
  simp only [CollatzResearch.WordTrace]
  refine ⟨1722710801386587880057061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4593895470364234346818829 1722710801386587880057061)
  ·
    refine ⟨323008275259985227510699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1722710801386587880057061 323008275259985227510699)
    ·
      refine ⟨484512412889977841266049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323008275259985227510699 484512412889977841266049)
      ·
        refine ⟨363384309667483380949537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 484512412889977841266049 363384309667483380949537)
        ·
          refine ⟨272538232250612535712153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363384309667483380949537 272538232250612535712153)
          ·
            refine ⟨204403674187959401784115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272538232250612535712153 204403674187959401784115)
            ·
              refine ⟨306605511281939102676173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204403674187959401784115 306605511281939102676173)
              ·
                refine ⟨114977066730727163503565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306605511281939102676173 114977066730727163503565)
                ·
                  refine ⟨43116400024022686313837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114977066730727163503565 43116400024022686313837)
                  ·
                    rfl

theorem cell21_188930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_188930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_188930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_188930 prefixEnd_188930 := by exact prefixLift 188930
  have htrace : WordTrace (prefixWord ++ tailWord_188930) baseStart_188930 baseEnd_188930 := by
    simpa [prefixWord, tailWord_188930, baseEnd_188930] using wordTrace_append hprefix tailTrace_188930
  have hstable : (prefixWord ++ tailWord_188930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188930).length < 2 ^ (prefixWord ++ tailWord_188930).sum := by decide
  have hdescent : baseEnd_188930 < baseStart_188930 := by decide
  rcases family_descends (prefixWord ++ tailWord_188930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188941 : List Nat := [1, 7, 1, 1, 1, 1, 9]
def baseStart_188941 : Nat := 118140960795 + 188941 * 2 ^ 59
def prefixEnd_188941 : Nat := 4983230072969 + 3 ^ 40 * 188941 * 2
def baseEnd_188941 : Nat := 4790990041543234625609

theorem tailTrace_188941 : CollatzResearch.WordTrace tailWord_188941 prefixEnd_188941 4790990041543234625609 := by
  unfold tailWord_188941
  simp only [CollatzResearch.WordTrace]
  refine ⟨6891244408506500398878677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4594162939004333599252451 6891244408506500398878677)
  ·
    refine ⟨161513540824371103098719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 6891244408506500398878677 161513540824371103098719)
    ·
      refine ⟨242270311236556654648079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161513540824371103098719 242270311236556654648079)
      ·
        refine ⟨363405466854834981972119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242270311236556654648079 363405466854834981972119)
        ·
          refine ⟨545108200282252472958179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363405466854834981972119 545108200282252472958179)
          ·
            refine ⟨817662300423378709437269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545108200282252472958179 817662300423378709437269)
            ·
              refine ⟨4790990041543234625609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 817662300423378709437269 4790990041543234625609)
              ·
                rfl

theorem cell21_188941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 9].length) (baseStart_188941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_188941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_188941 prefixEnd_188941 := by exact prefixLift 188941
  have htrace : WordTrace (prefixWord ++ tailWord_188941) baseStart_188941 baseEnd_188941 := by
    simpa [prefixWord, tailWord_188941, baseEnd_188941] using wordTrace_append hprefix tailTrace_188941
  have hstable : (prefixWord ++ tailWord_188941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188941).length < 2 ^ (prefixWord ++ tailWord_188941).sum := by decide
  have hdescent : baseEnd_188941 < baseStart_188941 := by decide
  rcases family_descends (prefixWord ++ tailWord_188941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189107 : List Nat := [1, 1, 1, 2, 3, 4, 3, 3, 3]
def baseStart_189107 : Nat := 118140960795 + 189107 * 2 ^ 59
def prefixEnd_189107 : Nat := 4983230072969 + 3 ^ 40 * 189107 * 2
def baseEnd_189107 : Nat := 43156793835509711863475

theorem tailTrace_189107 : CollatzResearch.WordTrace tailWord_189107 prefixEnd_189107 43156793835509711863475 := by
  unfold tailWord_189107
  simp only [CollatzResearch.WordTrace]
  refine ⟨6897298925905110749421575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4598199283936740499614383 6897298925905110749421575)
  ·
    refine ⟨10345948388857666124132363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6897298925905110749421575 10345948388857666124132363)
    ·
      refine ⟨15518922583286499186198545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10345948388857666124132363 15518922583286499186198545)
      ·
        refine ⟨11639191937464874389648909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15518922583286499186198545 11639191937464874389648909)
        ·
          refine ⟨4364696976549327896118341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11639191937464874389648909 4364696976549327896118341)
          ·
            refine ⟨818380683102998980522189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4364696976549327896118341 818380683102998980522189)
            ·
              refine ⟨306892756163624617695821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 818380683102998980522189 306892756163624617695821)
              ·
                refine ⟨115084783561359231635933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306892756163624617695821 115084783561359231635933)
                ·
                  refine ⟨43156793835509711863475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115084783561359231635933 43156793835509711863475)
                  ·
                    rfl

theorem cell21_189107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3, 3].length) (baseStart_189107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_189107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_189107 prefixEnd_189107 := by exact prefixLift 189107
  have htrace : WordTrace (prefixWord ++ tailWord_189107) baseStart_189107 baseEnd_189107 := by
    simpa [prefixWord, tailWord_189107, baseEnd_189107] using wordTrace_append hprefix tailTrace_189107
  have hstable : (prefixWord ++ tailWord_189107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189107).length < 2 ^ (prefixWord ++ tailWord_189107).sum := by decide
  have hdescent : baseEnd_189107 < baseStart_189107 := by decide
  rcases family_descends (prefixWord ++ tailWord_189107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189110 : List Nat := [5, 1, 3, 1, 3, 1, 7]
def baseStart_189110 : Nat := 118140960795 + 189110 * 2 ^ 59
def prefixEnd_189110 : Nat := 4983230072969 + 3 ^ 40 * 189110 * 2
def baseEnd_189110 : Nat := 4795275386264708145941

theorem tailTrace_189110 : CollatzResearch.WordTrace tailWord_189110 prefixEnd_189110 4795275386264708145941 := by
  unfold tailWord_189110
  simp only [CollatzResearch.WordTrace]
  refine ⟨431088021555890141361299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4598272229929494841187189 431088021555890141361299)
  ·
    refine ⟨646632032333835212041949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 431088021555890141361299 646632032333835212041949)
    ·
      refine ⟨242487012125188204515731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 646632032333835212041949 242487012125188204515731)
      ·
        refine ⟨363730518187782306773597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242487012125188204515731 363730518187782306773597)
        ·
          refine ⟨136398944320418365040099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 363730518187782306773597 136398944320418365040099)
          ·
            refine ⟨204598416480627547560149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136398944320418365040099 204598416480627547560149)
            ·
              refine ⟨4795275386264708145941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 204598416480627547560149 4795275386264708145941)
              ·
                rfl

theorem cell21_189110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 7].length) (baseStart_189110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_189110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_189110 prefixEnd_189110 := by exact prefixLift 189110
  have htrace : WordTrace (prefixWord ++ tailWord_189110) baseStart_189110 baseEnd_189110 := by
    simpa [prefixWord, tailWord_189110, baseEnd_189110] using wordTrace_append hprefix tailTrace_189110
  have hstable : (prefixWord ++ tailWord_189110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189110).length < 2 ^ (prefixWord ++ tailWord_189110).sum := by decide
  have hdescent : baseEnd_189110 < baseStart_189110 := by decide
  rcases family_descends (prefixWord ++ tailWord_189110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189138 : List Nat := [3, 2, 2, 2, 3, 1, 1, 3, 4]
def baseStart_189138 : Nat := 118140960795 + 189138 * 2 ^ 59
def prefixEnd_189138 : Nat := 4983230072969 + 3 ^ 40 * 189138 * 2
def baseEnd_189138 : Nat := 43163868457860546846745

theorem tailTrace_189138 : CollatzResearch.WordTrace tailWord_189138 prefixEnd_189138 43163868457860546846745 := by
  unfold tailWord_189138
  simp only [CollatzResearch.WordTrace]
  refine ⟨1724607397198200760950017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4598953059195202029200045 1724607397198200760950017)
  ·
    refine ⟨1293455547898650570712513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1724607397198200760950017 1293455547898650570712513)
    ·
      refine ⟨970091660923987928034385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1293455547898650570712513 970091660923987928034385)
      ·
        refine ⟨727568745692990946025789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 970091660923987928034385 727568745692990946025789)
        ·
          refine ⟨272838279634871604759671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 727568745692990946025789 272838279634871604759671)
          ·
            refine ⟨409257419452307407139507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272838279634871604759671 409257419452307407139507)
            ·
              refine ⟨613886129178461110709261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 409257419452307407139507 613886129178461110709261)
              ·
                refine ⟨230207298441922916515973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 613886129178461110709261 230207298441922916515973)
                ·
                  refine ⟨43163868457860546846745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 230207298441922916515973 43163868457860546846745)
                  ·
                    rfl

theorem cell21_189138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_189138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_189138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_189138 prefixEnd_189138 := by exact prefixLift 189138
  have htrace : WordTrace (prefixWord ++ tailWord_189138) baseStart_189138 baseEnd_189138 := by
    simpa [prefixWord, tailWord_189138, baseEnd_189138] using wordTrace_append hprefix tailTrace_189138
  have hstable : (prefixWord ++ tailWord_189138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189138).length < 2 ^ (prefixWord ++ tailWord_189138).sum := by decide
  have hdescent : baseEnd_189138 < baseStart_189138 := by decide
  rcases family_descends (prefixWord ++ tailWord_189138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189172 : List Nat := [2, 6, 1, 1, 2, 1, 2, 2, 4]
def baseStart_189172 : Nat := 118140960795 + 189172 * 2 ^ 59
def prefixEnd_189172 : Nat := 4983230072969 + 3 ^ 40 * 189172 * 2
def baseEnd_189172 : Nat := 43171627721084043280009

theorem tailTrace_189172 : CollatzResearch.WordTrace tailWord_189172 prefixEnd_189172 43171627721084043280009 := by
  unfold tailWord_189172
  simp only [CollatzResearch.WordTrace]
  refine ⟨3449834835334813425268885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4599779780446417900358513 3449834835334813425268885)
  ·
    refine ⟨161711007906319379309479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3449834835334813425268885 161711007906319379309479)
    ·
      refine ⟨242566511859479068964219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161711007906319379309479 242566511859479068964219)
      ·
        refine ⟨363849767789218603446329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242566511859479068964219 363849767789218603446329)
        ·
          refine ⟨272887325841913952584747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363849767789218603446329 272887325841913952584747)
          ·
            refine ⟨409330988762870928877121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272887325841913952584747 409330988762870928877121)
            ·
              refine ⟨306998241572153196657841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 409330988762870928877121 306998241572153196657841)
              ·
                refine ⟨230248681179114897493381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 306998241572153196657841 230248681179114897493381)
                ·
                  refine ⟨43171627721084043280009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 230248681179114897493381 43171627721084043280009)
                  ·
                    rfl

theorem cell21_189172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_189172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_189172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_189172 prefixEnd_189172 := by exact prefixLift 189172
  have htrace : WordTrace (prefixWord ++ tailWord_189172) baseStart_189172 baseEnd_189172 := by
    simpa [prefixWord, tailWord_189172, baseEnd_189172] using wordTrace_append hprefix tailTrace_189172
  have hstable : (prefixWord ++ tailWord_189172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189172).length < 2 ^ (prefixWord ++ tailWord_189172).sum := by decide
  have hdescent : baseEnd_189172 < baseStart_189172 := by decide
  rcases family_descends (prefixWord ++ tailWord_189172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189276 : List Nat := [2, 2, 4, 2, 1, 1, 3, 3, 3]
def baseStart_189276 : Nat := 118140960795 + 189276 * 2 ^ 59
def prefixEnd_189276 : Nat := 4983230072969 + 3 ^ 40 * 189276 * 2
def baseEnd_189276 : Nat := 43195361938002973546463

theorem tailTrace_189276 : CollatzResearch.WordTrace tailWord_189276 prefixEnd_189276 43195361938002973546463 := by
  unfold tailWord_189276
  simp only [CollatzResearch.WordTrace]
  refine ⟨3451731431146426306161841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4602308574861901741549121 3451731431146426306161841)
  ·
    refine ⟨2588798573359819729621381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3451731431146426306161841 2588798573359819729621381)
    ·
      refine ⟨485399732504966199304009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2588798573359819729621381 485399732504966199304009)
      ·
        refine ⟨364049799378724649478007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 485399732504966199304009 364049799378724649478007)
        ·
          refine ⟨546074699068086974217011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364049799378724649478007 546074699068086974217011)
          ·
            refine ⟨819112048602130461325517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546074699068086974217011 819112048602130461325517)
            ·
              refine ⟨307167018225798922997069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 819112048602130461325517 307167018225798922997069)
              ·
                refine ⟨115187631834674596123901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 307167018225798922997069 115187631834674596123901)
                ·
                  refine ⟨43195361938002973546463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115187631834674596123901 43195361938002973546463)
                  ·
                    rfl

theorem cell21_189276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3, 3].length) (baseStart_189276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_189276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_189276 prefixEnd_189276 := by exact prefixLift 189276
  have htrace : WordTrace (prefixWord ++ tailWord_189276) baseStart_189276 baseEnd_189276 := by
    simpa [prefixWord, tailWord_189276, baseEnd_189276] using wordTrace_append hprefix tailTrace_189276
  have hstable : (prefixWord ++ tailWord_189276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189276).length < 2 ^ (prefixWord ++ tailWord_189276).sum := by decide
  have hdescent : baseEnd_189276 < baseStart_189276 := by decide
  rcases family_descends (prefixWord ++ tailWord_189276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189287 : List Nat := [1, 1, 5, 1, 2, 4, 7]
def baseStart_189287 : Nat := 118140960795 + 189287 * 2 ^ 59
def prefixEnd_189287 : Nat := 4983230072969 + 3 ^ 40 * 189287 * 2
def baseEnd_189287 : Nat := 4799763587541044318123

theorem tailTrace_189287 : CollatzResearch.WordTrace tailWord_189287 prefixEnd_189287 4799763587541044318123 := by
  unfold tailWord_189287
  simp only [CollatzResearch.WordTrace]
  refine ⟨6903864065253001490974115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4602576043502000993982743 6903864065253001490974115)
  ·
    refine ⟨10355796097879502236461173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6903864065253001490974115 10355796097879502236461173)
    ·
      refine ⟨970855884176203334668235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10355796097879502236461173 970855884176203334668235)
      ·
        refine ⟨1456283826264305002002353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 970855884176203334668235 1456283826264305002002353)
        ·
          refine ⟨1092212869698228751501765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1456283826264305002002353 1092212869698228751501765)
          ·
            refine ⟨204789913068417890906581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1092212869698228751501765 204789913068417890906581)
            ·
              refine ⟨4799763587541044318123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 204789913068417890906581 4799763587541044318123)
              ·
                rfl

theorem cell21_189287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 7].length) (baseStart_189287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_189287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_189287 prefixEnd_189287 := by exact prefixLift 189287
  have htrace : WordTrace (prefixWord ++ tailWord_189287) baseStart_189287 baseEnd_189287 := by
    simpa [prefixWord, tailWord_189287, baseEnd_189287] using wordTrace_append hprefix tailTrace_189287
  have hstable : (prefixWord ++ tailWord_189287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189287).length < 2 ^ (prefixWord ++ tailWord_189287).sum := by decide
  have hdescent : baseEnd_189287 < baseStart_189287 := by decide
  rcases family_descends (prefixWord ++ tailWord_189287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189484 : List Nat := [2, 2, 1, 1, 1, 2, 5, 3, 4]
def baseStart_189484 : Nat := 118140960795 + 189484 * 2 ^ 59
def prefixEnd_189484 : Nat := 4983230072969 + 3 ^ 40 * 189484 * 2
def baseEnd_189484 : Nat := 43242830371840834079371

theorem tailTrace_189484 : CollatzResearch.WordTrace tailWord_189484 prefixEnd_189484 43242830371840834079371 := by
  unfold tailWord_189484
  simp only [CollatzResearch.WordTrace]
  refine ⟨3455524622769652067947753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4607366163692869423930337 3455524622769652067947753)
  ·
    refine ⟨2591643467077239050960815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3455524622769652067947753 2591643467077239050960815)
    ·
      refine ⟨3887465200615858576441223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2591643467077239050960815 3887465200615858576441223)
      ·
        refine ⟨5831197800923787864661835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3887465200615858576441223 5831197800923787864661835)
        ·
          refine ⟨8746796701385681796992753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5831197800923787864661835 8746796701385681796992753)
          ·
            refine ⟨6560097526039261347744565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8746796701385681796992753 6560097526039261347744565)
            ·
              refine ⟨615009143066180751351053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6560097526039261347744565 615009143066180751351053)
              ·
                refine ⟨230628428649817781756645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 615009143066180751351053 230628428649817781756645)
                ·
                  refine ⟨43242830371840834079371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 230628428649817781756645 43242830371840834079371)
                  ·
                    rfl

theorem cell21_189484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_189484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_189484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_189484 prefixEnd_189484 := by exact prefixLift 189484
  have htrace : WordTrace (prefixWord ++ tailWord_189484) baseStart_189484 baseEnd_189484 := by
    simpa [prefixWord, tailWord_189484, baseEnd_189484] using wordTrace_append hprefix tailTrace_189484
  have hstable : (prefixWord ++ tailWord_189484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189484).length < 2 ^ (prefixWord ++ tailWord_189484).sum := by decide
  have hdescent : baseEnd_189484 < baseStart_189484 := by decide
  rcases family_descends (prefixWord ++ tailWord_189484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189498 : List Nat := [3, 1, 1, 1, 3, 1, 4, 7]
def baseStart_189498 : Nat := 118140960795 + 189498 * 2 ^ 59
def prefixEnd_189498 : Nat := 4983230072969 + 3 ^ 40 * 189498 * 2
def baseEnd_189498 : Nat := 14415341787526640282003

theorem tailTrace_189498 : CollatzResearch.WordTrace tailWord_189498 prefixEnd_189498 14415341787526640282003 := by
  unfold tailWord_189498
  simp only [CollatzResearch.WordTrace]
  refine ⟨1727889966872146131726287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4607706578325723017936765 1727889966872146131726287)
  ·
    refine ⟨2591834950308219197589431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1727889966872146131726287 2591834950308219197589431)
    ·
      refine ⟨3887752425462328796384147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2591834950308219197589431 3887752425462328796384147)
      ·
        refine ⟨5831628638193493194576221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3887752425462328796384147 5831628638193493194576221)
        ·
          refine ⟨2186860739322559947966083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5831628638193493194576221 2186860739322559947966083)
          ·
            refine ⟨3280291108983839921949125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2186860739322559947966083 3280291108983839921949125)
            ·
              refine ⟨615054582934469985365461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3280291108983839921949125 615054582934469985365461)
              ·
                refine ⟨14415341787526640282003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 615054582934469985365461 14415341787526640282003)
                ·
                  rfl

theorem cell21_189498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_189498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_189498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_189498 prefixEnd_189498 := by exact prefixLift 189498
  have htrace : WordTrace (prefixWord ++ tailWord_189498) baseStart_189498 baseEnd_189498 := by
    simpa [prefixWord, tailWord_189498, baseEnd_189498] using wordTrace_append hprefix tailTrace_189498
  have hstable : (prefixWord ++ tailWord_189498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189498).length < 2 ^ (prefixWord ++ tailWord_189498).sum := by decide
  have hdescent : baseEnd_189498 < baseStart_189498 := by decide
  rcases family_descends (prefixWord ++ tailWord_189498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189546 : List Nat := [3, 1, 3, 2, 2, 2, 1, 2, 5]
def baseStart_189546 : Nat := 118140960795 + 189546 * 2 ^ 59
def prefixEnd_189546 : Nat := 4983230072969 + 3 ^ 40 * 189546 * 2
def baseEnd_189546 : Nat := 43256979616542504045911

theorem tailTrace_189546 : CollatzResearch.WordTrace tailWord_189546 prefixEnd_189546 43256979616542504045911 := by
  unfold tailWord_189546
  simp only [CollatzResearch.WordTrace]
  refine ⟨1728327642828672181163123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4608873714209792483101661 1728327642828672181163123)
  ·
    refine ⟨2592491464243008271744685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1728327642828672181163123 2592491464243008271744685)
    ·
      refine ⟨972184299091128101904257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2592491464243008271744685 972184299091128101904257)
      ·
        refine ⟨729138224318346076428193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 972184299091128101904257 729138224318346076428193)
        ·
          refine ⟨546853668238759557321145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 729138224318346076428193 546853668238759557321145)
          ·
            refine ⟨410140251179069667990859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 546853668238759557321145 410140251179069667990859)
            ·
              refine ⟨615210376768604501986289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410140251179069667990859 615210376768604501986289)
              ·
                refine ⟨461407782576453376489717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 615210376768604501986289 461407782576453376489717)
                ·
                  refine ⟨43256979616542504045911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 461407782576453376489717 43256979616542504045911)
                  ·
                    rfl

theorem cell21_189546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_189546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_189546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_189546 prefixEnd_189546 := by exact prefixLift 189546
  have htrace : WordTrace (prefixWord ++ tailWord_189546) baseStart_189546 baseEnd_189546 := by
    simpa [prefixWord, tailWord_189546, baseEnd_189546] using wordTrace_append hprefix tailTrace_189546
  have hstable : (prefixWord ++ tailWord_189546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189546).length < 2 ^ (prefixWord ++ tailWord_189546).sum := by decide
  have hdescent : baseEnd_189546 < baseStart_189546 := by decide
  rcases family_descends (prefixWord ++ tailWord_189546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189577 : List Nat := [1, 2, 1, 1, 4, 5, 1, 2, 4]
def baseStart_189577 : Nat := 118140960795 + 189577 * 2 ^ 59
def prefixEnd_189577 : Nat := 4983230072969 + 3 ^ 40 * 189577 * 2
def baseEnd_189577 : Nat := 43264054238893339029181

theorem tailTrace_189577 : CollatzResearch.WordTrace tailWord_189577 prefixEnd_189577 43264054238893339029181 := by
  unfold tailWord_189577
  simp only [CollatzResearch.WordTrace]
  refine ⟨6914441234202381019030985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4609627489468254012687323 6914441234202381019030985)
  ·
    refine ⟨5185830925651785764273239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6914441234202381019030985 5185830925651785764273239)
    ·
      refine ⟨7778746388477678646409859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5185830925651785764273239 7778746388477678646409859)
      ·
        refine ⟨11668119582716517969614789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7778746388477678646409859 11668119582716517969614789)
        ·
          refine ⟨2187772421759347119302773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11668119582716517969614789 2187772421759347119302773)
          ·
            refine ⟨205103664539938792434635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2187772421759347119302773 205103664539938792434635)
            ·
              refine ⟨307655496809908188651953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205103664539938792434635 307655496809908188651953)
              ·
                refine ⟨230741622607431141488965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 307655496809908188651953 230741622607431141488965)
                ·
                  refine ⟨43264054238893339029181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 230741622607431141488965 43264054238893339029181)
                  ·
                    rfl

theorem cell21_189577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 4].length) (baseStart_189577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_189577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_189577 prefixEnd_189577 := by exact prefixLift 189577
  have htrace : WordTrace (prefixWord ++ tailWord_189577) baseStart_189577 baseEnd_189577 := by
    simpa [prefixWord, tailWord_189577, baseEnd_189577] using wordTrace_append hprefix tailTrace_189577
  have hstable : (prefixWord ++ tailWord_189577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189577).length < 2 ^ (prefixWord ++ tailWord_189577).sum := by decide
  have hdescent : baseEnd_189577 < baseStart_189577 := by decide
  rcases family_descends (prefixWord ++ tailWord_189577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189594 : List Nat := [3, 1, 1, 5, 1, 2, 3, 1, 4]
def baseStart_189594 : Nat := 118140960795 + 189594 * 2 ^ 59
def prefixEnd_189594 : Nat := 4983230072969 + 3 ^ 40 * 189594 * 2
def baseEnd_189594 : Nat := 43267933870505087245813

theorem tailTrace_189594 : CollatzResearch.WordTrace tailWord_189594 prefixEnd_189594 43267933870505087245813 := by
  unfold tailWord_189594
  simp only [CollatzResearch.WordTrace]
  refine ⟨1728765318785198230599959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4610040850093861948266557 1728765318785198230599959)
  ·
    refine ⟨2593147978177797345899939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1728765318785198230599959 2593147978177797345899939)
    ·
      refine ⟨3889721967266696018849909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2593147978177797345899939 3889721967266696018849909)
      ·
        refine ⟨364661434431252751767179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3889721967266696018849909 364661434431252751767179)
        ·
          refine ⟨546992151646879127650769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364661434431252751767179 546992151646879127650769)
          ·
            refine ⟨410244113735159345738077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 546992151646879127650769 410244113735159345738077)
            ·
              refine ⟨153841542650684754651779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 410244113735159345738077 153841542650684754651779)
              ·
                refine ⟨230762313976027131977669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153841542650684754651779 230762313976027131977669)
                ·
                  refine ⟨43267933870505087245813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 230762313976027131977669 43267933870505087245813)
                  ·
                    rfl

theorem cell21_189594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_189594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_189594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_189594 prefixEnd_189594 := by exact prefixLift 189594
  have htrace : WordTrace (prefixWord ++ tailWord_189594) baseStart_189594 baseEnd_189594 := by
    simpa [prefixWord, tailWord_189594, baseEnd_189594] using wordTrace_append hprefix tailTrace_189594
  have hstable : (prefixWord ++ tailWord_189594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189594).length < 2 ^ (prefixWord ++ tailWord_189594).sum := by decide
  have hdescent : baseEnd_189594 < baseStart_189594 := by decide
  rcases family_descends (prefixWord ++ tailWord_189594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189605 : List Nat := [1, 3, 1, 2, 1, 4, 2, 2, 5]
def baseStart_189605 : Nat := 118140960795 + 189605 * 2 ^ 59
def prefixEnd_189605 : Nat := 4983230072969 + 3 ^ 40 * 189605 * 2
def baseEnd_189605 : Nat := 43270444220371512562457

theorem tailTrace_189605 : CollatzResearch.WordTrace tailWord_189605 prefixEnd_189605 43270444220371512562457 := by
  unfold tailWord_189605
  simp only [CollatzResearch.WordTrace]
  refine ⟨6915462478100941801050269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4610308318733961200700179 6915462478100941801050269)
  ·
    refine ⟨2593298429287853175393851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6915462478100941801050269 2593298429287853175393851)
    ·
      refine ⟨3889947643931779763090777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2593298429287853175393851 3889947643931779763090777)
      ·
        refine ⟨2917460732948834822318083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3889947643931779763090777 2917460732948834822318083)
        ·
          refine ⟨4376191099423252233477125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2917460732948834822318083 4376191099423252233477125)
          ·
            refine ⟨820535831141859793776961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4376191099423252233477125 820535831141859793776961)
            ·
              refine ⟨615401873356394845332721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 820535831141859793776961 615401873356394845332721)
              ·
                refine ⟨461551405017296133999541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 615401873356394845332721 461551405017296133999541)
                ·
                  refine ⟨43270444220371512562457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 461551405017296133999541 43270444220371512562457)
                  ·
                    rfl

theorem cell21_189605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_189605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_189605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_189605 prefixEnd_189605 := by exact prefixLift 189605
  have htrace : WordTrace (prefixWord ++ tailWord_189605) baseStart_189605 baseEnd_189605 := by
    simpa [prefixWord, tailWord_189605, baseEnd_189605] using wordTrace_append hprefix tailTrace_189605
  have hstable : (prefixWord ++ tailWord_189605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189605).length < 2 ^ (prefixWord ++ tailWord_189605).sum := by decide
  have hdescent : baseEnd_189605 < baseStart_189605 := by decide
  rcases family_descends (prefixWord ++ tailWord_189605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189619 : List Nat := [1, 1, 1, 2, 3, 2, 3, 2, 6]
def baseStart_189619 : Nat := 118140960795 + 189619 * 2 ^ 59
def prefixEnd_189619 : Nat := 4983230072969 + 3 ^ 40 * 189619 * 2
def baseEnd_189619 : Nat := 43273639211110599329095

theorem tailTrace_189619 : CollatzResearch.WordTrace tailWord_189619 prefixEnd_189619 43273639211110599329095 := by
  unfold tailWord_189619
  simp only [CollatzResearch.WordTrace]
  refine ⟨6915973100050222192059911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4610648733366814794706607 6915973100050222192059911)
  ·
    refine ⟨10373959650075333288089867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6915973100050222192059911 10373959650075333288089867)
    ·
      refine ⟨15560939475112999932134801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10373959650075333288089867 15560939475112999932134801)
      ·
        refine ⟨11670704606334749949101101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15560939475112999932134801 11670704606334749949101101)
        ·
          refine ⟨4376514227375531230912913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11670704606334749949101101 4376514227375531230912913)
          ·
            refine ⟨3282385670531648423184685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4376514227375531230912913 3282385670531648423184685)
            ·
              refine ⟨1230894626449368158694257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3282385670531648423184685 1230894626449368158694257)
              ·
                refine ⟨923170969837026119020693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1230894626449368158694257 923170969837026119020693)
                ·
                  refine ⟨43273639211110599329095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 923170969837026119020693 43273639211110599329095)
                  ·
                    rfl

theorem cell21_189619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 6].length) (baseStart_189619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_189619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_189619 prefixEnd_189619 := by exact prefixLift 189619
  have htrace : WordTrace (prefixWord ++ tailWord_189619) baseStart_189619 baseEnd_189619 := by
    simpa [prefixWord, tailWord_189619, baseEnd_189619] using wordTrace_append hprefix tailTrace_189619
  have hstable : (prefixWord ++ tailWord_189619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189619).length < 2 ^ (prefixWord ++ tailWord_189619).sum := by decide
  have hdescent : baseEnd_189619 < baseStart_189619 := by decide
  rcases family_descends (prefixWord ++ tailWord_189619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189645 : List Nat := [1, 6, 2, 2, 2, 1, 2, 1, 4]
def baseStart_189645 : Nat := 118140960795 + 189645 * 2 ^ 59
def prefixEnd_189645 : Nat := 4983230072969 + 3 ^ 40 * 189645 * 2
def baseEnd_189645 : Nat := 43279572765340331895709

theorem tailTrace_189645 : CollatzResearch.WordTrace tailWord_189645 prefixEnd_189645 43279572765340331895709 := by
  unfold tailWord_189645
  simp only [CollatzResearch.WordTrace]
  refine ⟨6916921397956028632506389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4611280931970685755004259 6916921397956028632506389)
  ·
    refine ⟨324230690529188842148737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6916921397956028632506389 324230690529188842148737)
    ·
      refine ⟨243173017896891631611553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324230690529188842148737 243173017896891631611553)
      ·
        refine ⟨182379763422668723708665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243173017896891631611553 182379763422668723708665)
        ·
          refine ⟨136784822567001542781499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182379763422668723708665 136784822567001542781499)
          ·
            refine ⟨205177233850502314172249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136784822567001542781499 205177233850502314172249)
            ·
              refine ⟨153882925387876735629187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205177233850502314172249 153882925387876735629187)
              ·
                refine ⟨230824388081815103443781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153882925387876735629187 230824388081815103443781)
                ·
                  refine ⟨43279572765340331895709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 230824388081815103443781 43279572765340331895709)
                  ·
                    rfl

theorem cell21_189645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_189645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_189645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_189645 prefixEnd_189645 := by exact prefixLift 189645
  have htrace : WordTrace (prefixWord ++ tailWord_189645) baseStart_189645 baseEnd_189645 := by
    simpa [prefixWord, tailWord_189645, baseEnd_189645] using wordTrace_append hprefix tailTrace_189645
  have hstable : (prefixWord ++ tailWord_189645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189645).length < 2 ^ (prefixWord ++ tailWord_189645).sum := by decide
  have hdescent : baseEnd_189645 < baseStart_189645 := by decide
  rcases family_descends (prefixWord ++ tailWord_189645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189653 : List Nat := [1, 3, 2, 4, 1, 2, 1, 3, 4]
def baseStart_189653 : Nat := 118140960795 + 189653 * 2 ^ 59
def prefixEnd_189653 : Nat := 4983230072969 + 3 ^ 40 * 189653 * 2
def baseEnd_189653 : Nat := 43281398474334095762359

theorem tailTrace_189653 : CollatzResearch.WordTrace tailWord_189653 prefixEnd_189653 43281398474334095762359 := by
  unfold tailWord_189653
  simp only [CollatzResearch.WordTrace]
  refine ⟨6917213181927045998797613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4611475454618030665865075 6917213181927045998797613)
  ·
    refine ⟨2593954943222642249549105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6917213181927045998797613 2593954943222642249549105)
    ·
      refine ⟨1945466207416981687161829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2593954943222642249549105 1945466207416981687161829)
      ·
        refine ⟨364774913890684066342843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1945466207416981687161829 364774913890684066342843)
        ·
          refine ⟨547162370836026099514265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364774913890684066342843 547162370836026099514265)
          ·
            refine ⟨410371778127019574635699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 547162370836026099514265 410371778127019574635699)
            ·
              refine ⟨615557667190529361953549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410371778127019574635699 615557667190529361953549)
              ·
                refine ⟨230834125196448510732581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 615557667190529361953549 230834125196448510732581)
                ·
                  refine ⟨43281398474334095762359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 230834125196448510732581 43281398474334095762359)
                  ·
                    rfl

theorem cell21_189653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_189653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_189653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_189653 prefixEnd_189653 := by exact prefixLift 189653
  have htrace : WordTrace (prefixWord ++ tailWord_189653) baseStart_189653 baseEnd_189653 := by
    simpa [prefixWord, tailWord_189653, baseEnd_189653] using wordTrace_append hprefix tailTrace_189653
  have hstable : (prefixWord ++ tailWord_189653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189653).length < 2 ^ (prefixWord ++ tailWord_189653).sum := by decide
  have hdescent : baseEnd_189653 < baseStart_189653 := by decide
  rcases family_descends (prefixWord ++ tailWord_189653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189684 : List Nat := [2, 6, 1, 2, 10]
def baseStart_189684 : Nat := 118140960795 + 189684 * 2 ^ 59
def prefixEnd_189684 : Nat := 4983230072969 + 3 ^ 40 * 189684 * 2
def baseEnd_189684 : Nat := 534425593786233712909

theorem tailTrace_189684 : CollatzResearch.WordTrace tailWord_189684 prefixEnd_189684 534425593786233712909 := by
  unfold tailWord_189684
  simp only [CollatzResearch.WordTrace]
  refine ⟨3459171922407369146588053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4612229229876492195450737 3459171922407369146588053)
  ·
    refine ⟨162148683862845428746315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3459171922407369146588053 162148683862845428746315)
    ·
      refine ⟨243223025794268143119473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162148683862845428746315 243223025794268143119473)
      ·
        refine ⟨182417269345701107339605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243223025794268143119473 182417269345701107339605)
        ·
          refine ⟨534425593786233712909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 182417269345701107339605 534425593786233712909)
          ·
            rfl

theorem cell21_189684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 10].length) (baseStart_189684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_189684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_189684 prefixEnd_189684 := by exact prefixLift 189684
  have htrace : WordTrace (prefixWord ++ tailWord_189684) baseStart_189684 baseEnd_189684 := by
    simpa [prefixWord, tailWord_189684, baseEnd_189684] using wordTrace_append hprefix tailTrace_189684
  have hstable : (prefixWord ++ tailWord_189684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189684).length < 2 ^ (prefixWord ++ tailWord_189684).sum := by decide
  have hdescent : baseEnd_189684 < baseStart_189684 := by decide
  rcases family_descends (prefixWord ++ tailWord_189684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189740 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 9]
def baseStart_189740 : Nat := 118140960795 + 189740 * 2 ^ 59
def prefixEnd_189740 : Nat := 4983230072969 + 3 ^ 40 * 189740 * 2
def baseEnd_189740 : Nat := 43301253059641277812181

theorem tailTrace_189740 : CollatzResearch.WordTrace tailWord_189740 prefixEnd_189740 43301253059641277812181 := by
  unfold tailWord_189740
  simp only [CollatzResearch.WordTrace]
  refine ⟨3460193166305929928607337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4613590888407906571476449 3460193166305929928607337)
  ·
    refine ⟨2595144874729447446455503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3460193166305929928607337 2595144874729447446455503)
    ·
      refine ⟨3892717312094171169683255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2595144874729447446455503 3892717312094171169683255)
      ·
        refine ⟨5839075968141256754524883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3892717312094171169683255 5839075968141256754524883)
        ·
          refine ⟨8758613952211885131787325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5839075968141256754524883 8758613952211885131787325)
          ·
            refine ⟨3284480232079456924420247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8758613952211885131787325 3284480232079456924420247)
            ·
              refine ⟨4926720348119185386630371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3284480232079456924420247 4926720348119185386630371)
              ·
                refine ⟨7390080522178778079945557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4926720348119185386630371 7390080522178778079945557)
                ·
                  refine ⟨43301253059641277812181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7390080522178778079945557 43301253059641277812181)
                  ·
                    rfl

theorem cell21_189740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_189740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_189740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_189740 prefixEnd_189740 := by exact prefixLift 189740
  have htrace : WordTrace (prefixWord ++ tailWord_189740) baseStart_189740 baseEnd_189740 := by
    simpa [prefixWord, tailWord_189740, baseEnd_189740] using wordTrace_append hprefix tailTrace_189740
  have hstable : (prefixWord ++ tailWord_189740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189740).length < 2 ^ (prefixWord ++ tailWord_189740).sum := by decide
  have hdescent : baseEnd_189740 < baseStart_189740 := by decide
  rcases family_descends (prefixWord ++ tailWord_189740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189850 : List Nat := [3, 1, 1, 4, 1, 1, 2, 5, 3]
def baseStart_189850 : Nat := 118140960795 + 189850 * 2 ^ 59
def prefixEnd_189850 : Nat := 4983230072969 + 3 ^ 40 * 189850 * 2
def baseEnd_189850 : Nat := 43326356558305530978623

theorem tailTrace_189850 : CollatzResearch.WordTrace tailWord_189850 prefixEnd_189850 43326356558305530978623 := by
  unfold tailWord_189850
  simp only [CollatzResearch.WordTrace]
  refine ⟨1731099590553337160929751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4616265574808899095812669 1731099590553337160929751)
  ·
    refine ⟨2596649385830005741394627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1731099590553337160929751 2596649385830005741394627)
    ·
      refine ⟨3894974078745008612091941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2596649385830005741394627 3894974078745008612091941)
      ·
        refine ⟨730307639764689114767239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3894974078745008612091941 730307639764689114767239)
        ·
          refine ⟨1095461459647033672150859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730307639764689114767239 1095461459647033672150859)
          ·
            refine ⟨1643192189470550508226289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1095461459647033672150859 1643192189470550508226289)
            ·
              refine ⟨1232394142102912881169717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1643192189470550508226289 1232394142102912881169717)
              ·
                refine ⟨115536950822148082609661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1232394142102912881169717 115536950822148082609661)
                ·
                  refine ⟨43326356558305530978623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115536950822148082609661 43326356558305530978623)
                  ·
                    rfl

theorem cell21_189850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5, 3].length) (baseStart_189850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_189850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_189850 prefixEnd_189850 := by exact prefixLift 189850
  have htrace : WordTrace (prefixWord ++ tailWord_189850) baseStart_189850 baseEnd_189850 := by
    simpa [prefixWord, tailWord_189850, baseEnd_189850] using wordTrace_append hprefix tailTrace_189850
  have hstable : (prefixWord ++ tailWord_189850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189850).length < 2 ^ (prefixWord ++ tailWord_189850).sum := by decide
  have hdescent : baseEnd_189850 < baseStart_189850 := by decide
  rcases family_descends (prefixWord ++ tailWord_189850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189985 : List Nat := [1, 2, 3, 2, 2, 2, 3, 1, 5]
def baseStart_189985 : Nat := 118140960795 + 189985 * 2 ^ 59
def prefixEnd_189985 : Nat := 4983230072969 + 3 ^ 40 * 189985 * 2
def baseEnd_189985 : Nat := 43357165397575296228347

theorem tailTrace_189985 : CollatzResearch.WordTrace tailWord_189985 prefixEnd_189985 43357165397575296228347 := by
  unfold tailWord_189985
  simp only [CollatzResearch.WordTrace]
  refine ⟨6929322216724266699883409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4619548144482844466588939 6929322216724266699883409)
  ·
    refine ⟨5196991662543200024912557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6929322216724266699883409 5196991662543200024912557)
    ·
      refine ⟨1948871873453700009342209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5196991662543200024912557 1948871873453700009342209)
      ·
        refine ⟨1461653905090275007006657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1948871873453700009342209 1461653905090275007006657)
        ·
          refine ⟨1096240428817706255254993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1461653905090275007006657 1096240428817706255254993)
          ·
            refine ⟨822180321613279691441245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1096240428817706255254993 822180321613279691441245)
            ·
              refine ⟨308317620604979884290467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 822180321613279691441245 308317620604979884290467)
              ·
                refine ⟨462476430907469826435701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308317620604979884290467 462476430907469826435701)
                ·
                  refine ⟨43357165397575296228347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 462476430907469826435701 43357165397575296228347)
                  ·
                    rfl

theorem cell21_189985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 5].length) (baseStart_189985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_189985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_189985 prefixEnd_189985 := by exact prefixLift 189985
  have htrace : WordTrace (prefixWord ++ tailWord_189985) baseStart_189985 baseEnd_189985 := by
    simpa [prefixWord, tailWord_189985, baseEnd_189985] using wordTrace_append hprefix tailTrace_189985
  have hstable : (prefixWord ++ tailWord_189985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189985).length < 2 ^ (prefixWord ++ tailWord_189985).sum := by decide
  have hdescent : baseEnd_189985 < baseStart_189985 := by decide
  rcases family_descends (prefixWord ++ tailWord_189985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190146 : List Nat := [3, 5, 1, 2, 1, 1, 3, 2, 3]
def baseStart_190146 : Nat := 118140960795 + 190146 * 2 ^ 59
def prefixEnd_190146 : Nat := 4983230072969 + 3 ^ 40 * 190146 * 2
def baseEnd_190146 : Nat := 43393907791074794044685

theorem tailTrace_190146 : CollatzResearch.WordTrace tailWord_190146 prefixEnd_190146 43393907791074794044685 := by
  unfold tailWord_190146
  simp only [CollatzResearch.WordTrace]
  refine ⟨1733798592285247799123573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4623462912760660797662861 1733798592285247799123573)
  ·
    refine ⟨162543618026741981167835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1733798592285247799123573 162543618026741981167835)
    ·
      refine ⟨243815427040112971751753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162543618026741981167835 243815427040112971751753)
      ·
        refine ⟨182861570280084728813815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243815427040112971751753 182861570280084728813815)
        ·
          refine ⟨274292355420127093220723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182861570280084728813815 274292355420127093220723)
          ·
            refine ⟨411438533130190639831085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274292355420127093220723 411438533130190639831085)
            ·
              refine ⟨154289449923821489936657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 411438533130190639831085 154289449923821489936657)
              ·
                refine ⟨115717087442866117452493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154289449923821489936657 115717087442866117452493)
                ·
                  refine ⟨43393907791074794044685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115717087442866117452493 43393907791074794044685)
                  ·
                    rfl

theorem cell21_190146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_190146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_190146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_190146 prefixEnd_190146 := by exact prefixLift 190146
  have htrace : WordTrace (prefixWord ++ tailWord_190146) baseStart_190146 baseEnd_190146 := by
    simpa [prefixWord, tailWord_190146, baseEnd_190146] using wordTrace_append hprefix tailTrace_190146
  have hstable : (prefixWord ++ tailWord_190146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190146).length < 2 ^ (prefixWord ++ tailWord_190146).sum := by decide
  have hdescent : baseEnd_190146 < baseStart_190146 := by decide
  rcases family_descends (prefixWord ++ tailWord_190146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190151 : List Nat := [1, 1, 4, 1, 1, 1, 4, 4, 4]
def baseStart_190151 : Nat := 118140960795 + 190151 * 2 ^ 59
def prefixEnd_190151 : Nat := 4983230072969 + 3 ^ 40 * 190151 * 2
def baseEnd_190151 : Nat := 43395048859195896461341

theorem tailTrace_190151 : CollatzResearch.WordTrace tailWord_190151 prefixEnd_190151 43395048859195896461341 := by
  unfold tailWord_190151
  simp only [CollatzResearch.WordTrace]
  refine ⟨6935376734122877050426307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4623584489415251366950871 6935376734122877050426307)
  ·
    refine ⟨10403065101184315575639461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6935376734122877050426307 10403065101184315575639461)
    ·
      refine ⟨1950574706472059170432399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10403065101184315575639461 1950574706472059170432399)
      ·
        refine ⟨2925862059708088755648599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1950574706472059170432399 2925862059708088755648599)
        ·
          refine ⟨4388793089562133133472899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2925862059708088755648599 4388793089562133133472899)
          ·
            refine ⟨6583189634343199700209349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4388793089562133133472899 6583189634343199700209349)
            ·
              refine ⟨1234348056439349943789253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6583189634343199700209349 1234348056439349943789253)
              ·
                refine ⟨231440260582378114460485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1234348056439349943789253 231440260582378114460485)
                ·
                  refine ⟨43395048859195896461341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 231440260582378114460485 43395048859195896461341)
                  ·
                    rfl

theorem cell21_190151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 4].length) (baseStart_190151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_190151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_190151 prefixEnd_190151 := by exact prefixLift 190151
  have htrace : WordTrace (prefixWord ++ tailWord_190151) baseStart_190151 baseEnd_190151 := by
    simpa [prefixWord, tailWord_190151, baseEnd_190151] using wordTrace_append hprefix tailTrace_190151
  have hstable : (prefixWord ++ tailWord_190151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190151).length < 2 ^ (prefixWord ++ tailWord_190151).sum := by decide
  have hdescent : baseEnd_190151 < baseStart_190151 := by decide
  rcases family_descends (prefixWord ++ tailWord_190151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190154 : List Nat := [3, 1, 2, 1, 5, 2, 1, 1, 5]
def baseStart_190154 : Nat := 118140960795 + 190154 * 2 ^ 59
def prefixEnd_190154 : Nat := 4983230072969 + 3 ^ 40 * 190154 * 2
def baseEnd_190154 : Nat := 43395733500068557911335

theorem tailTrace_190154 : CollatzResearch.WordTrace tailWord_190154 prefixEnd_190154 43395733500068557911335 := by
  unfold tailWord_190154
  simp only [CollatzResearch.WordTrace]
  refine ⟨1733871538278002140696379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4623657435408005708523677 1733871538278002140696379)
  ·
    refine ⟨2600807307417003211044569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1733871538278002140696379 2600807307417003211044569)
    ·
      refine ⟨1950605480562752408283427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2600807307417003211044569 1950605480562752408283427)
      ·
        refine ⟨2925908220844128612425141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1950605480562752408283427 2925908220844128612425141)
        ·
          refine ⟨274303895704137057414857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2925908220844128612425141 274303895704137057414857)
          ·
            refine ⟨205727921778102793061143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274303895704137057414857 205727921778102793061143)
            ·
              refine ⟨308591882667154189591715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205727921778102793061143 308591882667154189591715)
              ·
                refine ⟨462887824000731284387573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308591882667154189591715 462887824000731284387573)
                ·
                  refine ⟨43395733500068557911335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 462887824000731284387573 43395733500068557911335)
                  ·
                    rfl

theorem cell21_190154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_190154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_190154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_190154 prefixEnd_190154 := by exact prefixLift 190154
  have htrace : WordTrace (prefixWord ++ tailWord_190154) baseStart_190154 baseEnd_190154 := by
    simpa [prefixWord, tailWord_190154, baseEnd_190154] using wordTrace_append hprefix tailTrace_190154
  have hstable : (prefixWord ++ tailWord_190154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190154).length < 2 ^ (prefixWord ++ tailWord_190154).sum := by decide
  have hdescent : baseEnd_190154 < baseStart_190154 := by decide
  rcases family_descends (prefixWord ++ tailWord_190154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190261 : List Nat := [1, 3, 3, 1, 4, 2, 1, 2, 4]
def baseStart_190261 : Nat := 118140960795 + 190261 * 2 ^ 59
def prefixEnd_190261 : Nat := 4983230072969 + 3 ^ 40 * 190261 * 2
def baseEnd_190261 : Nat := 43420152357860149627783

theorem tailTrace_190261 : CollatzResearch.WordTrace tailWord_190261 prefixEnd_190261 43420152357860149627783 := by
  unfold tailWord_190261
  simp only [CollatzResearch.WordTrace]
  refine ⟨6939388763724365836930637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4626259175816243891287091 6939388763724365836930637)
  ·
    refine ⟨2602270786396637188848989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6939388763724365836930637 2602270786396637188848989)
    ·
      refine ⟨975851544898738945818371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2602270786396637188848989 975851544898738945818371)
      ·
        refine ⟨1463777317348108418727557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 975851544898738945818371 1463777317348108418727557)
        ·
          refine ⟨274458247002770328511417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1463777317348108418727557 274458247002770328511417)
          ·
            refine ⟨205843685252077746383563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274458247002770328511417 205843685252077746383563)
            ·
              refine ⟨308765527878116619575345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205843685252077746383563 308765527878116619575345)
              ·
                refine ⟨231574145908587464681509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308765527878116619575345 231574145908587464681509)
                ·
                  refine ⟨43420152357860149627783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 231574145908587464681509 43420152357860149627783)
                  ·
                    rfl

theorem cell21_190261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_190261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_190261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_190261 prefixEnd_190261 := by exact prefixLift 190261
  have htrace : WordTrace (prefixWord ++ tailWord_190261) baseStart_190261 baseEnd_190261 := by
    simpa [prefixWord, tailWord_190261, baseEnd_190261] using wordTrace_append hprefix tailTrace_190261
  have hstable : (prefixWord ++ tailWord_190261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190261).length < 2 ^ (prefixWord ++ tailWord_190261).sum := by decide
  have hdescent : baseEnd_190261 < baseStart_190261 := by decide
  rcases family_descends (prefixWord ++ tailWord_190261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190317 : List Nat := [1, 5, 1, 1, 1, 1, 11]
def baseStart_190317 : Nat := 118140960795 + 190317 * 2 ^ 59
def prefixEnd_190317 : Nat := 4983230072969 + 3 ^ 40 * 190317 * 2
def baseEnd_190317 : Nat := 4825881368979610743815

theorem tailTrace_190317 : CollatzResearch.WordTrace tailWord_190317 prefixEnd_190317 4825881368979610743815 := by
  unfold tailWord_190317
  simp only [CollatzResearch.WordTrace]
  refine ⟨6941431251521487400969205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4627620834347658267312803 6941431251521487400969205)
  ·
    refine ⟨650759179830139443840863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6941431251521487400969205 650759179830139443840863)
    ·
      refine ⟨976138769745209165761295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 650759179830139443840863 976138769745209165761295)
      ·
        refine ⟨1464208154617813748641943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 976138769745209165761295 1464208154617813748641943)
        ·
          refine ⟨2196312231926720622962915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1464208154617813748641943 2196312231926720622962915)
          ·
            refine ⟨3294468347890080934444373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2196312231926720622962915 3294468347890080934444373)
            ·
              refine ⟨4825881368979610743815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 3294468347890080934444373 4825881368979610743815)
              ·
                rfl

theorem cell21_190317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 11].length) (baseStart_190317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_190317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_190317 prefixEnd_190317 := by exact prefixLift 190317
  have htrace : WordTrace (prefixWord ++ tailWord_190317) baseStart_190317 baseEnd_190317 := by
    simpa [prefixWord, tailWord_190317, baseEnd_190317] using wordTrace_append hprefix tailTrace_190317
  have hstable : (prefixWord ++ tailWord_190317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190317).length < 2 ^ (prefixWord ++ tailWord_190317).sum := by decide
  have hdescent : baseEnd_190317 < baseStart_190317 := by decide
  rcases family_descends (prefixWord ++ tailWord_190317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190337 : List Nat := [1, 2, 4, 4, 1, 1, 1, 3, 4]
def baseStart_190337 : Nat := 118140960795 + 190337 * 2 ^ 59
def prefixEnd_190337 : Nat := 4983230072969 + 3 ^ 40 * 190337 * 2
def baseEnd_190337 : Nat := 43437496593300906360961

theorem tailTrace_190337 : CollatzResearch.WordTrace tailWord_190337 prefixEnd_190337 43437496593300906360961 := by
  unfold tailWord_190337
  simp only [CollatzResearch.WordTrace]
  refine ⟨6942160711449030816697265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4628107140966020544464843 6942160711449030816697265)
  ·
    refine ⟨5206620533586773112522949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6942160711449030816697265 5206620533586773112522949)
    ·
      refine ⟨976241350047519958598053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5206620533586773112522949 976241350047519958598053)
      ·
        refine ⟨183045253133909992237135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 976241350047519958598053 183045253133909992237135)
        ·
          refine ⟨274567879700864988355703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183045253133909992237135 274567879700864988355703)
          ·
            refine ⟨411851819551297482533555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274567879700864988355703 411851819551297482533555)
            ·
              refine ⟨617777729326946223800333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411851819551297482533555 617777729326946223800333)
              ·
                refine ⟨231666648497604833925125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 617777729326946223800333 231666648497604833925125)
                ·
                  refine ⟨43437496593300906360961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 231666648497604833925125 43437496593300906360961)
                  ·
                    rfl

theorem cell21_190337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 4].length) (baseStart_190337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_190337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_190337 prefixEnd_190337 := by exact prefixLift 190337
  have htrace : WordTrace (prefixWord ++ tailWord_190337) baseStart_190337 baseEnd_190337 := by
    simpa [prefixWord, tailWord_190337, baseEnd_190337] using wordTrace_append hprefix tailTrace_190337
  have hstable : (prefixWord ++ tailWord_190337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190337).length < 2 ^ (prefixWord ++ tailWord_190337).sum := by decide
  have hdescent : baseEnd_190337 < baseStart_190337 := by decide
  rcases family_descends (prefixWord ++ tailWord_190337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190469 : List Nat := [1, 3, 1, 1, 2, 5, 1, 7]
def baseStart_190469 : Nat := 118140960795 + 190469 * 2 ^ 59
def prefixEnd_190469 : Nat := 4983230072969 + 3 ^ 40 * 190469 * 2
def baseEnd_190469 : Nat := 14489206930566003386897

theorem tailTrace_190469 : CollatzResearch.WordTrace tailWord_190469 prefixEnd_190469 14489206930566003386897 := by
  unfold tailWord_190469
  simp only [CollatzResearch.WordTrace]
  refine ⟨6946975146970817360502461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4631316764647211573668307 6946975146970817360502461)
  ·
    refine ⟨2605115680114056510188423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6946975146970817360502461 2605115680114056510188423)
    ·
      refine ⟨3907673520171084765282635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2605115680114056510188423 3907673520171084765282635)
      ·
        refine ⟨5861510280256627147923953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3907673520171084765282635 5861510280256627147923953)
        ·
          refine ⟨4396132710192470360942965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5861510280256627147923953 4396132710192470360942965)
          ·
            refine ⟨412137441580544096338403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4396132710192470360942965 412137441580544096338403)
            ·
              refine ⟨618206162370816144507605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412137441580544096338403 618206162370816144507605)
              ·
                refine ⟨14489206930566003386897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 618206162370816144507605 14489206930566003386897)
                ·
                  rfl

theorem cell21_190469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 7].length) (baseStart_190469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_190469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_190469 prefixEnd_190469 := by exact prefixLift 190469
  have htrace : WordTrace (prefixWord ++ tailWord_190469) baseStart_190469 baseEnd_190469 := by
    simpa [prefixWord, tailWord_190469, baseEnd_190469] using wordTrace_append hprefix tailTrace_190469
  have hstable : (prefixWord ++ tailWord_190469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190469).length < 2 ^ (prefixWord ++ tailWord_190469).sum := by decide
  have hdescent : baseEnd_190469 < baseStart_190469 := by decide
  rcases family_descends (prefixWord ++ tailWord_190469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190483 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 7]
def baseStart_190483 : Nat := 118140960795 + 190483 * 2 ^ 59
def prefixEnd_190483 : Nat := 4983230072969 + 3 ^ 40 * 190483 * 2
def baseEnd_190483 : Nat := 43470815782437096927329

theorem tailTrace_190483 : CollatzResearch.WordTrace tailWord_190483 prefixEnd_190483 43470815782437096927329 := by
  unfold tailWord_190483
  simp only [CollatzResearch.WordTrace]
  refine ⟨6947485768920097751512103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4631657179280065167674735 6947485768920097751512103)
  ·
    refine ⟨10421228653380146627268155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6947485768920097751512103 10421228653380146627268155)
    ·
      refine ⟨15631842980070219940902233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10421228653380146627268155 15631842980070219940902233)
      ·
        refine ⟨11723882235052664955676675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15631842980070219940902233 11723882235052664955676675)
        ·
          refine ⟨17585823352578997433515013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11723882235052664955676675 17585823352578997433515013)
          ·
            refine ⟨3297341878608562018784065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17585823352578997433515013 3297341878608562018784065)
            ·
              refine ⟨2473006408956421514088049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3297341878608562018784065 2473006408956421514088049)
              ·
                refine ⟨1854754806717316135566037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2473006408956421514088049 1854754806717316135566037)
                ·
                  refine ⟨43470815782437096927329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1854754806717316135566037 43470815782437096927329)
                  ·
                    rfl

theorem cell21_190483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 7].length) (baseStart_190483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_190483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_190483 prefixEnd_190483 := by exact prefixLift 190483
  have htrace : WordTrace (prefixWord ++ tailWord_190483) baseStart_190483 baseEnd_190483 := by
    simpa [prefixWord, tailWord_190483, baseEnd_190483] using wordTrace_append hprefix tailTrace_190483
  have hstable : (prefixWord ++ tailWord_190483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190483).length < 2 ^ (prefixWord ++ tailWord_190483).sum := by decide
  have hdescent : baseEnd_190483 < baseStart_190483 := by decide
  rcases family_descends (prefixWord ++ tailWord_190483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190503 : List Nat := [1, 1, 7, 1, 2, 1, 2, 6]
def baseStart_190503 : Nat := 118140960795 + 190503 * 2 ^ 59
def prefixEnd_190503 : Nat := 4983230072969 + 3 ^ 40 * 190503 * 2
def baseEnd_190503 : Nat := 14491793351640502197985

theorem tailTrace_190503 : CollatzResearch.WordTrace tailWord_190503 prefixEnd_190503 14491793351640502197985 := by
  unfold tailWord_190503
  simp only [CollatzResearch.WordTrace]
  refine ⟨6948215228847641167240163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4632143485898427444826775 6948215228847641167240163)
  ·
    refine ⟨10422322843271461750860245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6948215228847641167240163 10422322843271461750860245)
    ·
      refine ⟨244273191639174884785787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 10422322843271461750860245 244273191639174884785787)
      ·
        refine ⟨366409787458762327178681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244273191639174884785787 366409787458762327178681)
        ·
          refine ⟨274807340594071745384011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366409787458762327178681 274807340594071745384011)
          ·
            refine ⟨412211010891107618076017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274807340594071745384011 412211010891107618076017)
            ·
              refine ⟨309158258168330713557013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 412211010891107618076017 309158258168330713557013)
              ·
                refine ⟨14491793351640502197985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 309158258168330713557013 14491793351640502197985)
                ·
                  rfl

theorem cell21_190503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 6].length) (baseStart_190503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_190503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_190503 prefixEnd_190503 := by exact prefixLift 190503
  have htrace : WordTrace (prefixWord ++ tailWord_190503) baseStart_190503 baseEnd_190503 := by
    simpa [prefixWord, tailWord_190503, baseEnd_190503] using wordTrace_append hprefix tailTrace_190503
  have hstable : (prefixWord ++ tailWord_190503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190503).length < 2 ^ (prefixWord ++ tailWord_190503).sum := by decide
  have hdescent : baseEnd_190503 < baseStart_190503 := by decide
  rcases family_descends (prefixWord ++ tailWord_190503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190576 : List Nat := [2, 1, 1, 1, 5, 3, 1, 2, 5]
def baseStart_190576 : Nat := 118140960795 + 190576 * 2 ^ 59
def prefixEnd_190576 : Nat := 4983230072969 + 3 ^ 40 * 190576 * 2
def baseEnd_190576 : Nat := 43492039649489601877139

theorem tailTrace_190576 : CollatzResearch.WordTrace tailWord_190576 prefixEnd_190576 43492039649489601877139 := by
  unfold tailWord_190576
  simp only [CollatzResearch.WordTrace]
  refine ⟨3475438878791587317323791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4633918505055449756431721 3475438878791587317323791)
  ·
    refine ⟨5213158318187380975985687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3475438878791587317323791 5213158318187380975985687)
    ·
      refine ⟨7819737477281071463978531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5213158318187380975985687 7819737477281071463978531)
      ·
        refine ⟨11729606215921607195967797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7819737477281071463978531 11729606215921607195967797)
        ·
          refine ⟨1099650582742650674621981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11729606215921607195967797 1099650582742650674621981)
          ·
            refine ⟨412368968528494002983243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1099650582742650674621981 412368968528494002983243)
            ·
              refine ⟨618553452792741004474865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412368968528494002983243 618553452792741004474865)
              ·
                refine ⟨463915089594555753356149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 618553452792741004474865 463915089594555753356149)
                ·
                  refine ⟨43492039649489601877139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 463915089594555753356149 43492039649489601877139)
                  ·
                    rfl

theorem cell21_190576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 5].length) (baseStart_190576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_190576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_190576 prefixEnd_190576 := by exact prefixLift 190576
  have htrace : WordTrace (prefixWord ++ tailWord_190576) baseStart_190576 baseEnd_190576 := by
    simpa [prefixWord, tailWord_190576, baseEnd_190576] using wordTrace_append hprefix tailTrace_190576
  have hstable : (prefixWord ++ tailWord_190576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190576).length < 2 ^ (prefixWord ++ tailWord_190576).sum := by decide
  have hdescent : baseEnd_190576 < baseStart_190576 := by decide
  rcases family_descends (prefixWord ++ tailWord_190576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190624 : List Nat := [2, 1, 1, 4, 2, 3, 3, 1, 4]
def baseStart_190624 : Nat := 118140960795 + 190624 * 2 ^ 59
def prefixEnd_190624 : Nat := 4983230072969 + 3 ^ 40 * 190624 * 2
def baseEnd_190624 : Nat := 43502993903452185077041

theorem tailTrace_190624 : CollatzResearch.WordTrace tailWord_190624 prefixEnd_190624 43502993903452185077041 := by
  unfold tailWord_190624
  simp only [CollatzResearch.WordTrace]
  refine ⟨3476314230704639416197463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4635085640939519221596617 3476314230704639416197463)
  ·
    refine ⟨5214471346056959124296195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3476314230704639416197463 5214471346056959124296195)
    ·
      refine ⟨7821707019085438686444293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5214471346056959124296195 7821707019085438686444293)
      ·
        refine ⟨1466570066078519753708305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7821707019085438686444293 1466570066078519753708305)
        ·
          refine ⟨1099927549558889815281229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1466570066078519753708305 1099927549558889815281229)
          ·
            refine ⟨412472831084583680730461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1099927549558889815281229 412472831084583680730461)
            ·
              refine ⟨154677311656718880273923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 412472831084583680730461 154677311656718880273923)
              ·
                refine ⟨232015967485078320410885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154677311656718880273923 232015967485078320410885)
                ·
                  refine ⟨43502993903452185077041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 232015967485078320410885 43502993903452185077041)
                  ·
                    rfl

theorem cell21_190624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 4].length) (baseStart_190624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_190624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_190624 prefixEnd_190624 := by exact prefixLift 190624
  have htrace : WordTrace (prefixWord ++ tailWord_190624) baseStart_190624 baseEnd_190624 := by
    simpa [prefixWord, tailWord_190624, baseEnd_190624] using wordTrace_append hprefix tailTrace_190624
  have hstable : (prefixWord ++ tailWord_190624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190624).length < 2 ^ (prefixWord ++ tailWord_190624).sum := by decide
  have hdescent : baseEnd_190624 < baseStart_190624 := by decide
  rcases family_descends (prefixWord ++ tailWord_190624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190666 : List Nat := [3, 1, 2, 1, 3, 1, 1, 3, 6]
def baseStart_190666 : Nat := 118140960795 + 190666 * 2 ^ 59
def prefixEnd_190666 : Nat := 4983230072969 + 3 ^ 40 * 190666 * 2
def baseEnd_190666 : Nat := 43512578875669445376955

theorem tailTrace_190666 : CollatzResearch.WordTrace tailWord_190666 prefixEnd_190666 43512578875669445376955 := by
  unfold tailWord_190666
  simp only [CollatzResearch.WordTrace]
  refine ⟨1738540081814280001355963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4636106884838080003615901 1738540081814280001355963)
  ·
    refine ⟨2607810122721420002033945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1738540081814280001355963 2607810122721420002033945)
    ·
      refine ⟨1955857592041065001525459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2607810122721420002033945 1955857592041065001525459)
      ·
        refine ⟨2933786388061597502288189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1955857592041065001525459 2933786388061597502288189)
        ·
          refine ⟨1100169895523099063358071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2933786388061597502288189 1100169895523099063358071)
          ·
            refine ⟨1650254843284648595037107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1100169895523099063358071 1650254843284648595037107)
            ·
              refine ⟨2475382264926972892555661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1650254843284648595037107 2475382264926972892555661)
              ·
                refine ⟨928268349347614834708373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2475382264926972892555661 928268349347614834708373)
                ·
                  refine ⟨43512578875669445376955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 928268349347614834708373 43512578875669445376955)
                  ·
                    rfl

theorem cell21_190666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_190666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_190666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_190666 prefixEnd_190666 := by exact prefixLift 190666
  have htrace : WordTrace (prefixWord ++ tailWord_190666) baseStart_190666 baseEnd_190666 := by
    simpa [prefixWord, tailWord_190666, baseEnd_190666] using wordTrace_append hprefix tailTrace_190666
  have hstable : (prefixWord ++ tailWord_190666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190666).length < 2 ^ (prefixWord ++ tailWord_190666).sum := by decide
  have hdescent : baseEnd_190666 < baseStart_190666 := by decide
  rcases family_descends (prefixWord ++ tailWord_190666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190787 : List Nat := [1, 1, 1, 3, 1, 3, 3, 3, 5]
def baseStart_190787 : Nat := 118140960795 + 190787 * 2 ^ 59
def prefixEnd_190787 : Nat := 4983230072969 + 3 ^ 40 * 190787 * 2
def baseEnd_190787 : Nat := 43540192724200123860041

theorem tailTrace_190787 : CollatzResearch.WordTrace tailWord_190787 prefixEnd_190787 43540192724200123860041 := by
  unfold tailWord_190787
  simp only [CollatzResearch.WordTrace]
  refine ⟨6958573559818757670578615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4639049039879171780385743 6958573559818757670578615)
  ·
    refine ⟨10437860339728136505867923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6958573559818757670578615 10437860339728136505867923)
    ·
      refine ⟨15656790509592204758801885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10437860339728136505867923 15656790509592204758801885)
      ·
        refine ⟨5871296441097076784550707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15656790509592204758801885 5871296441097076784550707)
        ·
          refine ⟨8806944661645615176826061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5871296441097076784550707 8806944661645615176826061)
          ·
            refine ⟨3302604248117105691309773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8806944661645615176826061 3302604248117105691309773)
            ·
              refine ⟨1238476593043914634241165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3302604248117105691309773 1238476593043914634241165)
              ·
                refine ⟨464428722391467987840437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1238476593043914634241165 464428722391467987840437)
                ·
                  refine ⟨43540192724200123860041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 464428722391467987840437 43540192724200123860041)
                  ·
                    rfl

theorem cell21_190787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 5].length) (baseStart_190787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_190787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_190787 prefixEnd_190787 := by exact prefixLift 190787
  have htrace : WordTrace (prefixWord ++ tailWord_190787) baseStart_190787 baseEnd_190787 := by
    simpa [prefixWord, tailWord_190787, baseEnd_190787] using wordTrace_append hprefix tailTrace_190787
  have hstable : (prefixWord ++ tailWord_190787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190787).length < 2 ^ (prefixWord ++ tailWord_190787).sum := by decide
  have hdescent : baseEnd_190787 < baseStart_190787 := by decide
  rcases family_descends (prefixWord ++ tailWord_190787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190804 : List Nat := [2, 4, 1, 1, 2, 2, 2, 2, 5]
def baseStart_190804 : Nat := 118140960795 + 190804 * 2 ^ 59
def prefixEnd_190804 : Nat := 4983230072969 + 3 ^ 40 * 190804 * 2
def baseEnd_190804 : Nat := 43544072355811872076673

theorem tailTrace_190804 : CollatzResearch.WordTrace tailWord_190804 prefixEnd_190804 43544072355811872076673 := by
  unfold tailWord_190804
  simp only [CollatzResearch.WordTrace]
  refine ⟨3479596800378584786973733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4639462400504779715964977 3479596800378584786973733)
  ·
    refine ⟨652424400070984647557575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3479596800378584786973733 652424400070984647557575)
    ·
      refine ⟨978636600106476971336363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 652424400070984647557575 978636600106476971336363)
      ·
        refine ⟨1467954900159715457004545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 978636600106476971336363 1467954900159715457004545)
        ·
          refine ⟨1100966175119786592753409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1467954900159715457004545 1100966175119786592753409)
          ·
            refine ⟨825724631339839944565057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1100966175119786592753409 825724631339839944565057)
            ·
              refine ⟨619293473504879958423793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 825724631339839944565057 619293473504879958423793)
              ·
                refine ⟨464470105128659968817845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 619293473504879958423793 464470105128659968817845)
                ·
                  refine ⟨43544072355811872076673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 464470105128659968817845 43544072355811872076673)
                  ·
                    rfl

theorem cell21_190804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_190804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_190804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_190804 prefixEnd_190804 := by exact prefixLift 190804
  have htrace : WordTrace (prefixWord ++ tailWord_190804) baseStart_190804 baseEnd_190804 := by
    simpa [prefixWord, tailWord_190804, baseEnd_190804] using wordTrace_append hprefix tailTrace_190804
  have hstable : (prefixWord ++ tailWord_190804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190804).length < 2 ^ (prefixWord ++ tailWord_190804).sum := by decide
  have hdescent : baseEnd_190804 < baseStart_190804 := by decide
  rcases family_descends (prefixWord ++ tailWord_190804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190821 : List Nat := [1, 3, 1, 3, 1, 3, 3, 3, 3]
def baseStart_190821 : Nat := 118140960795 + 190821 * 2 ^ 59
def prefixEnd_190821 : Nat := 4983230072969 + 3 ^ 40 * 190821 * 2
def baseEnd_190821 : Nat := 43547951987423620293305

theorem tailTrace_190821 : CollatzResearch.WordTrace tailWord_190821 prefixEnd_190821 43547951987423620293305 := by
  unfold tailWord_190821
  simp only [CollatzResearch.WordTrace]
  refine ⟨6959813641695581477316317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4639875761130387651544211 6959813641695581477316317)
  ·
    refine ⟨2609930115635843053993619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6959813641695581477316317 2609930115635843053993619)
    ·
      refine ⟨3914895173453764580990429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2609930115635843053993619 3914895173453764580990429)
      ·
        refine ⟨1468085690045161717871411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3914895173453764580990429 1468085690045161717871411)
        ·
          refine ⟨2202128535067742576807117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1468085690045161717871411 2202128535067742576807117)
          ·
            refine ⟨825798200650403466302669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2202128535067742576807117 825798200650403466302669)
            ·
              refine ⟨309674325243901299863501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 825798200650403466302669 309674325243901299863501)
              ·
                refine ⟨116127871966462987448813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 309674325243901299863501 116127871966462987448813)
                ·
                  refine ⟨43547951987423620293305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116127871966462987448813 43547951987423620293305)
                  ·
                    rfl

theorem cell21_190821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3, 3].length) (baseStart_190821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_190821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_190821 prefixEnd_190821 := by exact prefixLift 190821
  have htrace : WordTrace (prefixWord ++ tailWord_190821) baseStart_190821 baseEnd_190821 := by
    simpa [prefixWord, tailWord_190821, baseEnd_190821] using wordTrace_append hprefix tailTrace_190821
  have hstable : (prefixWord ++ tailWord_190821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190821).length < 2 ^ (prefixWord ++ tailWord_190821).sum := by decide
  have hdescent : baseEnd_190821 < baseStart_190821 := by decide
  rcases family_descends (prefixWord ++ tailWord_190821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190832 : List Nat := [2, 1, 1, 1, 4, 3, 9]
def baseStart_190832 : Nat := 118140960795 + 190832 * 2 ^ 59
def prefixEnd_190832 : Nat := 4983230072969 + 3 ^ 40 * 190832 * 2
def baseEnd_190832 : Nat := 4838940259698893956661

theorem tailTrace_190832 : CollatzResearch.WordTrace tailWord_190832 prefixEnd_190832 4838940259698893956661 := by
  unfold tailWord_190832
  simp only [CollatzResearch.WordTrace]
  refine ⟨3480107422327865177983375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4640143229770486903977833 3480107422327865177983375)
  ·
    refine ⟨5220161133491797766975063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3480107422327865177983375 5220161133491797766975063)
    ·
      refine ⟨7830241700237696650462595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5220161133491797766975063 7830241700237696650462595)
      ·
        refine ⟨11745362550356544975693893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7830241700237696650462595 11745362550356544975693893)
        ·
          refine ⟨2202255478191852182942605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11745362550356544975693893 2202255478191852182942605)
          ·
            refine ⟨825845804321944568603477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2202255478191852182942605 825845804321944568603477)
            ·
              refine ⟨4838940259698893956661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 825845804321944568603477 4838940259698893956661)
              ·
                rfl

theorem cell21_190832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 9].length) (baseStart_190832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_190832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_190832 prefixEnd_190832 := by exact prefixLift 190832
  have htrace : WordTrace (prefixWord ++ tailWord_190832) baseStart_190832 baseEnd_190832 := by
    simpa [prefixWord, tailWord_190832, baseEnd_190832] using wordTrace_append hprefix tailTrace_190832
  have hstable : (prefixWord ++ tailWord_190832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190832).length < 2 ^ (prefixWord ++ tailWord_190832).sum := by decide
  have hdescent : baseEnd_190832 < baseStart_190832 := by decide
  rcases family_descends (prefixWord ++ tailWord_190832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190849 : List Nat := [1, 2, 4, 3, 1, 1, 1, 8]
def baseStart_190849 : Nat := 118140960795 + 190849 * 2 ^ 59
def prefixEnd_190849 : Nat := 4983230072969 + 3 ^ 40 * 190849 * 2
def baseEnd_190849 : Nat := 14518113989633931275527

theorem tailTrace_190849 : CollatzResearch.WordTrace tailWord_190849 prefixEnd_190849 14518113989633931275527 := by
  unfold tailWord_190849
  simp only [CollatzResearch.WordTrace]
  refine ⟨6960834885594142259335601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4640556590396094839557067 6960834885594142259335601)
  ·
    refine ⟨5220626164195606694501701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6960834885594142259335601 5220626164195606694501701)
    ·
      refine ⟨978867405786676255219069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5220626164195606694501701 978867405786676255219069)
      ·
        refine ⟨367075277170003595707151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 978867405786676255219069 367075277170003595707151)
        ·
          refine ⟨550612915755005393560727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367075277170003595707151 550612915755005393560727)
          ·
            refine ⟨825919373632508090341091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550612915755005393560727 825919373632508090341091)
            ·
              refine ⟨1238879060448762135511637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 825919373632508090341091 1238879060448762135511637)
              ·
                refine ⟨14518113989633931275527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1238879060448762135511637 14518113989633931275527)
                ·
                  rfl

theorem cell21_190849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 8].length) (baseStart_190849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_190849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_190849 prefixEnd_190849 := by exact prefixLift 190849
  have htrace : WordTrace (prefixWord ++ tailWord_190849) baseStart_190849 baseEnd_190849 := by
    simpa [prefixWord, tailWord_190849, baseEnd_190849] using wordTrace_append hprefix tailTrace_190849
  have hstable : (prefixWord ++ tailWord_190849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190849).length < 2 ^ (prefixWord ++ tailWord_190849).sum := by decide
  have hdescent : baseEnd_190849 < baseStart_190849 := by decide
  rcases family_descends (prefixWord ++ tailWord_190849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190897 : List Nat := [1, 2, 2, 4, 1, 3, 1, 4, 3]
def baseStart_190897 : Nat := 118140960795 + 190897 * 2 ^ 59
def prefixEnd_190897 : Nat := 4983230072969 + 3 ^ 40 * 190897 * 2
def baseEnd_190897 : Nat := 43565296222864377026483

theorem tailTrace_190897 : CollatzResearch.WordTrace tailWord_190897 prefixEnd_190897 43565296222864377026483 := by
  unfold tailWord_190897
  simp only [CollatzResearch.WordTrace]
  refine ⟨6962585589420246457082945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4641723726280164304721963 6962585589420246457082945)
  ·
    refine ⟨5221939192065184842812209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6962585589420246457082945 5221939192065184842812209)
    ·
      refine ⟨3916454394048888632109157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5221939192065184842812209 3916454394048888632109157)
      ·
        refine ⟨734335198884166618520467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3916454394048888632109157 734335198884166618520467)
        ·
          refine ⟨1101502798326249927780701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 734335198884166618520467 1101502798326249927780701)
          ·
            refine ⟨413063549372343722917763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1101502798326249927780701 413063549372343722917763)
            ·
              refine ⟨619595324058515584376645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413063549372343722917763 619595324058515584376645)
              ·
                refine ⟨116174123260971672070621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 619595324058515584376645 116174123260971672070621)
                ·
                  refine ⟨43565296222864377026483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116174123260971672070621 43565296222864377026483)
                  ·
                    rfl

theorem cell21_190897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4, 3].length) (baseStart_190897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_190897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_190897 prefixEnd_190897 := by exact prefixLift 190897
  have htrace : WordTrace (prefixWord ++ tailWord_190897) baseStart_190897 baseEnd_190897 := by
    simpa [prefixWord, tailWord_190897, baseEnd_190897] using wordTrace_append hprefix tailTrace_190897
  have hstable : (prefixWord ++ tailWord_190897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190897).length < 2 ^ (prefixWord ++ tailWord_190897).sum := by decide
  have hdescent : baseEnd_190897 < baseStart_190897 := by decide
  rcases family_descends (prefixWord ++ tailWord_190897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190900 : List Nat := [2, 5, 2, 2, 1, 2, 1, 6]
def baseStart_190900 : Nat := 118140960795 + 190900 * 2 ^ 59
def prefixEnd_190900 : Nat := 4983230072969 + 3 ^ 40 * 190900 * 2
def baseEnd_190900 : Nat := 14521993621245679492159

theorem tailTrace_190900 : CollatzResearch.WordTrace tailWord_190900 prefixEnd_190900 14521993621245679492159 := by
  unfold tailWord_190900
  simp only [CollatzResearch.WordTrace]
  refine ⟨3481347504204688984721077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4641796672272918646294769 3481347504204688984721077)
  ·
    refine ⟨326376328519189592317601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3481347504204688984721077 326376328519189592317601)
    ·
      refine ⟨244782246389392194238201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326376328519189592317601 244782246389392194238201)
      ·
        refine ⟨183586684792044145678651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244782246389392194238201 183586684792044145678651)
        ·
          refine ⟨275380027188066218517977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183586684792044145678651 275380027188066218517977)
          ·
            refine ⟨206535020391049663888483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275380027188066218517977 206535020391049663888483)
            ·
              refine ⟨309802530586574495832725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206535020391049663888483 309802530586574495832725)
              ·
                refine ⟨14521993621245679492159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 309802530586574495832725 14521993621245679492159)
                ·
                  rfl

theorem cell21_190900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 6].length) (baseStart_190900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_190900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_190900 prefixEnd_190900 := by exact prefixLift 190900
  have htrace : WordTrace (prefixWord ++ tailWord_190900) baseStart_190900 baseEnd_190900 := by
    simpa [prefixWord, tailWord_190900, baseEnd_190900] using wordTrace_append hprefix tailTrace_190900
  have hstable : (prefixWord ++ tailWord_190900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190900).length < 2 ^ (prefixWord ++ tailWord_190900).sum := by decide
  have hdescent : baseEnd_190900 < baseStart_190900 := by decide
  rcases family_descends (prefixWord ++ tailWord_190900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190956 : List Nat := [2, 2, 1, 1, 2, 1, 3, 6, 3]
def baseStart_190956 : Nat := 118140960795 + 190956 * 2 ^ 59
def prefixEnd_190956 : Nat := 4983230072969 + 3 ^ 40 * 190956 * 2
def baseEnd_190956 : Nat := 43578760826693385543029

theorem tailTrace_190956 : CollatzResearch.WordTrace tailWord_190956 prefixEnd_190956 43578760826693385543029 := by
  unfold tailWord_190956
  simp only [CollatzResearch.WordTrace]
  refine ⟨3482368748103249766740361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4643158330804333022320481 3482368748103249766740361)
  ·
    refine ⟨2611776561077437325055271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3482368748103249766740361 2611776561077437325055271)
    ·
      refine ⟨3917664841616155987582907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2611776561077437325055271 3917664841616155987582907)
      ·
        refine ⟨5876497262424233981374361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3917664841616155987582907 5876497262424233981374361)
        ·
          refine ⟨4407372946818175486030771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5876497262424233981374361 4407372946818175486030771)
          ·
            refine ⟨6611059420227263229046157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4407372946818175486030771 6611059420227263229046157)
            ·
              refine ⟨2479147282585223710892309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6611059420227263229046157 2479147282585223710892309)
              ·
                refine ⟨116210028871182361448077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2479147282585223710892309 116210028871182361448077)
                ·
                  refine ⟨43578760826693385543029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116210028871182361448077 43578760826693385543029)
                  ·
                    rfl

theorem cell21_190956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6, 3].length) (baseStart_190956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_190956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_190956 prefixEnd_190956 := by exact prefixLift 190956
  have htrace : WordTrace (prefixWord ++ tailWord_190956) baseStart_190956 baseEnd_190956 := by
    simpa [prefixWord, tailWord_190956, baseEnd_190956] using wordTrace_append hprefix tailTrace_190956
  have hstable : (prefixWord ++ tailWord_190956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190956).length < 2 ^ (prefixWord ++ tailWord_190956).sum := by decide
  have hdescent : baseEnd_190956 < baseStart_190956 := by decide
  rcases family_descends (prefixWord ++ tailWord_190956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190990 : List Nat := [4, 1, 1, 2, 3, 3, 1, 3, 3]
def baseStart_190990 : Nat := 118140960795 + 190990 * 2 ^ 59
def prefixEnd_190990 : Nat := 4983230072969 + 3 ^ 40 * 190990 * 2
def baseEnd_190990 : Nat := 43586520089916881976293

theorem tailTrace_190990 : CollatzResearch.WordTrace tailWord_190990 prefixEnd_190990 43586520089916881976293 := by
  unfold tailWord_190990
  simp only [CollatzResearch.WordTrace]
  refine ⟨870747197260415417527303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4643985052055548893478949 870747197260415417527303)
  ·
    refine ⟨1306120795890623126290955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 870747197260415417527303 1306120795890623126290955)
    ·
      refine ⟨1959181193835934689436433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1306120795890623126290955 1959181193835934689436433)
      ·
        refine ⟨1469385895376951017077325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1959181193835934689436433 1469385895376951017077325)
        ·
          refine ⟨551019710766356631403997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1469385895376951017077325 551019710766356631403997)
          ·
            refine ⟨206632391537383736776499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 551019710766356631403997 206632391537383736776499)
            ·
              refine ⟨309948587306075605164749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206632391537383736776499 309948587306075605164749)
              ·
                refine ⟨116230720239778351936781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 309948587306075605164749 116230720239778351936781)
                ·
                  refine ⟨43586520089916881976293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116230720239778351936781 43586520089916881976293)
                  ·
                    rfl

theorem cell21_190990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_190990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_190990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_190990 prefixEnd_190990 := by exact prefixLift 190990
  have htrace : WordTrace (prefixWord ++ tailWord_190990) baseStart_190990 baseEnd_190990 := by
    simpa [prefixWord, tailWord_190990, baseEnd_190990] using wordTrace_append hprefix tailTrace_190990
  have hstable : (prefixWord ++ tailWord_190990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190990).length < 2 ^ (prefixWord ++ tailWord_190990).sum := by decide
  have hdescent : baseEnd_190990 < baseStart_190990 := by decide
  rcases family_descends (prefixWord ++ tailWord_190990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191060 : List Nat := [2, 4, 1, 1, 1, 12]
def baseStart_191060 : Nat := 118140960795 + 191060 * 2 ^ 59
def prefixEnd_191060 : Nat := 4983230072969 + 3 ^ 40 * 191060 * 2
def baseEnd_191060 : Nat := 1614907223837493178129

theorem tailTrace_191060 : CollatzResearch.WordTrace tailWord_191060 prefixEnd_191060 1614907223837493178129 := by
  unfold tailWord_191060
  simp only [CollatzResearch.WordTrace]
  refine ⟨3484265343914862647633317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4645687125219816863511089 3484265343914862647633317)
  ·
    refine ⟨653299751984036746431247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3484265343914862647633317 653299751984036746431247)
    ·
      refine ⟨979949627976055119646871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 653299751984036746431247 979949627976055119646871)
      ·
        refine ⟨1469924441964082679470307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 979949627976055119646871 1469924441964082679470307)
        ·
          refine ⟨2204886662946124019205461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1469924441964082679470307 2204886662946124019205461)
          ·
            refine ⟨1614907223837493178129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2204886662946124019205461 1614907223837493178129)
            ·
              rfl

theorem cell21_191060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 12].length) (baseStart_191060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_191060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_191060 prefixEnd_191060 := by exact prefixLift 191060
  have htrace : WordTrace (prefixWord ++ tailWord_191060) baseStart_191060 baseEnd_191060 := by
    simpa [prefixWord, tailWord_191060, baseEnd_191060] using wordTrace_append hprefix tailTrace_191060
  have hstable : (prefixWord ++ tailWord_191060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191060).length < 2 ^ (prefixWord ++ tailWord_191060).sum := by decide
  have hdescent : baseEnd_191060 < baseStart_191060 := by decide
  rcases family_descends (prefixWord ++ tailWord_191060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191319 : List Nat := [1, 1, 3, 2, 4, 1, 2, 2, 5]
def baseStart_191319 : Nat := 118140960795 + 191319 * 2 ^ 59
def prefixEnd_191319 : Nat := 4983230072969 + 3 ^ 40 * 191319 * 2
def baseEnd_191319 : Nat := 43661602372285420992287

theorem tailTrace_191319 : CollatzResearch.WordTrace tailWord_191319 prefixEnd_191319 43661602372285420992287 := by
  unfold tailWord_191319
  simp only [CollatzResearch.WordTrace]
  refine ⟨6977977193891412528945011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4651984795927608352630007 6977977193891412528945011)
  ·
    refine ⟨10466965790837118793417517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6977977193891412528945011 10466965790837118793417517)
    ·
      refine ⟨3925112171563919547531569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10466965790837118793417517 3925112171563919547531569)
      ·
        refine ⟨2943834128672939660648677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3925112171563919547531569 2943834128672939660648677)
        ·
          refine ⟨551968899126176186371627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2943834128672939660648677 551968899126176186371627)
          ·
            refine ⟨827953348689264279557441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551968899126176186371627 827953348689264279557441)
            ·
              refine ⟨620965011516948209668081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 827953348689264279557441 620965011516948209668081)
              ·
                refine ⟨465723758637711157251061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 620965011516948209668081 465723758637711157251061)
                ·
                  refine ⟨43661602372285420992287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 465723758637711157251061 43661602372285420992287)
                  ·
                    rfl

theorem cell21_191319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 5].length) (baseStart_191319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_191319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_191319 prefixEnd_191319 := by exact prefixLift 191319
  have htrace : WordTrace (prefixWord ++ tailWord_191319) baseStart_191319 baseEnd_191319 := by
    simpa [prefixWord, tailWord_191319, baseEnd_191319] using wordTrace_append hprefix tailTrace_191319
  have hstable : (prefixWord ++ tailWord_191319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191319).length < 2 ^ (prefixWord ++ tailWord_191319).sum := by decide
  have hdescent : baseEnd_191319 < baseStart_191319 := by decide
  rcases family_descends (prefixWord ++ tailWord_191319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191333 : List Nat := [1, 3, 1, 3, 1, 1, 3, 2, 6]
def baseStart_191333 : Nat := 118140960795 + 191333 * 2 ^ 59
def prefixEnd_191333 : Nat := 4983230072969 + 3 ^ 40 * 191333 * 2
def baseEnd_191333 : Nat := 43664797363024507758925

theorem tailTrace_191333 : CollatzResearch.WordTrace tailWord_191333 prefixEnd_191333 43664797363024507758925 := by
  unfold tailWord_191333
  simp only [CollatzResearch.WordTrace]
  refine ⟨6978487815840692919954653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4652325210560461946636435 6978487815840692919954653)
  ·
    refine ⟨2616932930940259844982995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6978487815840692919954653 2616932930940259844982995)
    ·
      refine ⟨3925399396410389767474493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2616932930940259844982995 3925399396410389767474493)
      ·
        refine ⟨1472024773653896162802935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3925399396410389767474493 1472024773653896162802935)
        ·
          refine ⟨2208037160480844244204403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1472024773653896162802935 2208037160480844244204403)
          ·
            refine ⟨3312055740721266366306605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2208037160480844244204403 3312055740721266366306605)
            ·
              refine ⟨1242020902770474887364977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3312055740721266366306605 1242020902770474887364977)
              ·
                refine ⟨931515677077856165523733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1242020902770474887364977 931515677077856165523733)
                ·
                  refine ⟨43664797363024507758925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 931515677077856165523733 43664797363024507758925)
                  ·
                    rfl

theorem cell21_191333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_191333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_191333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_191333 prefixEnd_191333 := by exact prefixLift 191333
  have htrace : WordTrace (prefixWord ++ tailWord_191333) baseStart_191333 baseEnd_191333 := by
    simpa [prefixWord, tailWord_191333, baseEnd_191333] using wordTrace_append hprefix tailTrace_191333
  have hstable : (prefixWord ++ tailWord_191333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191333).length < 2 ^ (prefixWord ++ tailWord_191333).sum := by decide
  have hdescent : baseEnd_191333 < baseStart_191333 := by decide
  rcases family_descends (prefixWord ++ tailWord_191333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191347 : List Nat := [1, 1, 1, 2, 2, 1, 13]
def baseStart_191347 : Nat := 118140960795 + 191347 * 2 ^ 59
def prefixEnd_191347 : Nat := 4983230072969 + 3 ^ 40 * 191347 * 2
def baseEnd_191347 : Nat := 4851999150418177169507

theorem tailTrace_191347 : CollatzResearch.WordTrace tailWord_191347 prefixEnd_191347 4851999150418177169507 := by
  unfold tailWord_191347
  simp only [CollatzResearch.WordTrace]
  refine ⟨6978998437789973310964295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4652665625193315540642863 6978998437789973310964295)
  ·
    refine ⟨10468497656684959966446443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6978998437789973310964295 10468497656684959966446443)
    ·
      refine ⟨15702746485027439949669665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10468497656684959966446443 15702746485027439949669665)
      ·
        refine ⟨11777059863770579962252249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15702746485027439949669665 11777059863770579962252249)
        ·
          refine ⟨8832794897827934971689187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11777059863770579962252249 8832794897827934971689187)
          ·
            refine ⟨13249192346741902457533781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8832794897827934971689187 13249192346741902457533781)
            ·
              refine ⟨4851999150418177169507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 13249192346741902457533781 4851999150418177169507)
              ·
                rfl

theorem cell21_191347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 13].length) (baseStart_191347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_191347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_191347 prefixEnd_191347 := by exact prefixLift 191347
  have htrace : WordTrace (prefixWord ++ tailWord_191347) baseStart_191347 baseEnd_191347 := by
    simpa [prefixWord, tailWord_191347, baseEnd_191347] using wordTrace_append hprefix tailTrace_191347
  have hstable : (prefixWord ++ tailWord_191347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191347).length < 2 ^ (prefixWord ++ tailWord_191347).sum := by decide
  have hdescent : baseEnd_191347 < baseStart_191347 := by decide
  rcases family_descends (prefixWord ++ tailWord_191347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191353 : List Nat := [1, 2, 1, 3, 2, 4, 3, 2, 3]
def baseStart_191353 : Nat := 118140960795 + 191353 * 2 ^ 59
def prefixEnd_191353 : Nat := 4983230072969 + 3 ^ 40 * 191353 * 2
def baseEnd_191353 : Nat := 43669361635508917425551

theorem tailTrace_191353 : CollatzResearch.WordTrace tailWord_191353 prefixEnd_191353 43669361635508917425551 := by
  unfold tailWord_191353
  simp only [CollatzResearch.WordTrace]
  refine ⟨6979217275768236335682713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4652811517178824223788475 6979217275768236335682713)
  ·
    refine ⟨5234412956826177251762035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6979217275768236335682713 5234412956826177251762035)
    ·
      refine ⟨7851619435239265877643053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5234412956826177251762035 7851619435239265877643053)
      ·
        refine ⟨2944357288214724704116145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7851619435239265877643053 2944357288214724704116145)
        ·
          refine ⟨2208267966161043528087109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2944357288214724704116145 2208267966161043528087109)
          ·
            refine ⟨414050243655195661516333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2208267966161043528087109 414050243655195661516333)
            ·
              refine ⟨155268841370698373068625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 414050243655195661516333 155268841370698373068625)
              ·
                refine ⟨116451631028023779801469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155268841370698373068625 116451631028023779801469)
                ·
                  refine ⟨43669361635508917425551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116451631028023779801469 43669361635508917425551)
                  ·
                    rfl

theorem cell21_191353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2, 3].length) (baseStart_191353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_191353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_191353 prefixEnd_191353 := by exact prefixLift 191353
  have htrace : WordTrace (prefixWord ++ tailWord_191353) baseStart_191353 baseEnd_191353 := by
    simpa [prefixWord, tailWord_191353, baseEnd_191353] using wordTrace_append hprefix tailTrace_191353
  have hstable : (prefixWord ++ tailWord_191353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191353).length < 2 ^ (prefixWord ++ tailWord_191353).sum := by decide
  have hdescent : baseEnd_191353 < baseStart_191353 := by decide
  rcases family_descends (prefixWord ++ tailWord_191353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191367 : List Nat := [1, 1, 4, 2, 3, 1, 4, 1, 4]
def baseStart_191367 : Nat := 118140960795 + 191367 * 2 ^ 59
def prefixEnd_191367 : Nat := 4983230072969 + 3 ^ 40 * 191367 * 2
def baseEnd_191367 : Nat := 43672556626248004192189

theorem tailTrace_191367 : CollatzResearch.WordTrace tailWord_191367 prefixEnd_191367 43672556626248004192189 := by
  unfold tailWord_191367
  simp only [CollatzResearch.WordTrace]
  refine ⟨6979727897717516726692355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4653151931811677817794903 6979727897717516726692355)
  ·
    refine ⟨10469591846576275090038533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6979727897717516726692355 10469591846576275090038533)
    ·
      refine ⟨1963048471233051579382225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10469591846576275090038533 1963048471233051579382225)
      ·
        refine ⟨1472286353424788684536669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1963048471233051579382225 1472286353424788684536669)
        ·
          refine ⟨552107382534295756701251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1472286353424788684536669 552107382534295756701251)
          ·
            refine ⟨828161073801443635051877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552107382534295756701251 828161073801443635051877)
            ·
              refine ⟨155280201337770681572227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 828161073801443635051877 155280201337770681572227)
              ·
                refine ⟨232920302006656022358341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155280201337770681572227 232920302006656022358341)
                ·
                  refine ⟨43672556626248004192189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 232920302006656022358341 43672556626248004192189)
                  ·
                    rfl

theorem cell21_191367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 4].length) (baseStart_191367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_191367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_191367 prefixEnd_191367 := by exact prefixLift 191367
  have htrace : WordTrace (prefixWord ++ tailWord_191367) baseStart_191367 baseEnd_191367 := by
    simpa [prefixWord, tailWord_191367, baseEnd_191367] using wordTrace_append hprefix tailTrace_191367
  have hstable : (prefixWord ++ tailWord_191367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191367).length < 2 ^ (prefixWord ++ tailWord_191367).sum := by decide
  have hdescent : baseEnd_191367 < baseStart_191367 := by decide
  rcases family_descends (prefixWord ++ tailWord_191367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191423 : List Nat := [1, 1, 2, 2, 2, 1, 2, 10]
def baseStart_191423 : Nat := 118140960795 + 191423 * 2 ^ 59
def prefixEnd_191423 : Nat := 4983230072969 + 3 ^ 40 * 191423 * 2
def baseEnd_191423 : Nat := 14561778863068117086247

theorem tailTrace_191423 : CollatzResearch.WordTrace tailWord_191423 prefixEnd_191423 14561778863068117086247 := by
  unfold tailWord_191423
  simp only [CollatzResearch.WordTrace]
  refine ⟨6981770385514638290730923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4654513590343092193820615 6981770385514638290730923)
  ·
    refine ⟨10472655578271957436096385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6981770385514638290730923 10472655578271957436096385)
    ·
      refine ⟨7854491683703968077072289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10472655578271957436096385 7854491683703968077072289)
      ·
        refine ⟨5890868762777976057804217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7854491683703968077072289 5890868762777976057804217)
        ·
          refine ⟨4418151572083482043353163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5890868762777976057804217 4418151572083482043353163)
          ·
            refine ⟨6627227358125223065029745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4418151572083482043353163 6627227358125223065029745)
            ·
              refine ⟨4970420518593917298772309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6627227358125223065029745 4970420518593917298772309)
              ·
                refine ⟨14561778863068117086247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4970420518593917298772309 14561778863068117086247)
                ·
                  rfl

theorem cell21_191423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 10].length) (baseStart_191423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_191423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_191423 prefixEnd_191423 := by exact prefixLift 191423
  have htrace : WordTrace (prefixWord ++ tailWord_191423) baseStart_191423 baseEnd_191423 := by
    simpa [prefixWord, tailWord_191423, baseEnd_191423] using wordTrace_append hprefix tailTrace_191423
  have hstable : (prefixWord ++ tailWord_191423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191423).length < 2 ^ (prefixWord ++ tailWord_191423).sum := by decide
  have hdescent : baseEnd_191423 < baseStart_191423 := by decide
  rcases family_descends (prefixWord ++ tailWord_191423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191446 : List Nat := [5, 2, 1, 1, 2, 2, 2, 3, 3]
def baseStart_191446 : Nat := 118140960795 + 191446 * 2 ^ 59
def prefixEnd_191446 : Nat := 4983230072969 + 3 ^ 40 * 191446 * 2
def baseEnd_191446 : Nat := 43690585502561422375361

theorem tailTrace_191446 : CollatzResearch.WordTrace tailWord_191446 prefixEnd_191446 43690585502561422375361 := by
  unfold tailWord_191446
  simp only [CollatzResearch.WordTrace]
  refine ⟨436413079026957076176137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4655072842954208812545461 436413079026957076176137)
  ·
    refine ⟨327309809270217807132103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 436413079026957076176137 327309809270217807132103)
    ·
      refine ⟨490964713905326710698155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327309809270217807132103 490964713905326710698155)
      ·
        refine ⟨736447070857990066047233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490964713905326710698155 736447070857990066047233)
        ·
          refine ⟨552335303143492549535425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 736447070857990066047233 552335303143492549535425)
          ·
            refine ⟨414251477357619412151569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 552335303143492549535425 414251477357619412151569)
            ·
              refine ⟨310688608018214559113677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414251477357619412151569 310688608018214559113677)
              ·
                refine ⟨116508228006830459667629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310688608018214559113677 116508228006830459667629)
                ·
                  refine ⟨43690585502561422375361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116508228006830459667629 43690585502561422375361)
                  ·
                    rfl

theorem cell21_191446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_191446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_191446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_191446 prefixEnd_191446 := by exact prefixLift 191446
  have htrace : WordTrace (prefixWord ++ tailWord_191446) baseStart_191446 baseEnd_191446 := by
    simpa [prefixWord, tailWord_191446, baseEnd_191446] using wordTrace_append hprefix tailTrace_191446
  have hstable : (prefixWord ++ tailWord_191446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191446).length < 2 ^ (prefixWord ++ tailWord_191446).sum := by decide
  have hdescent : baseEnd_191446 < baseStart_191446 := by decide
  rcases family_descends (prefixWord ++ tailWord_191446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191471 : List Nat := [1, 1, 2, 1, 4, 4, 2, 1, 5]
def baseStart_191471 : Nat := 118140960795 + 191471 * 2 ^ 59
def prefixEnd_191471 : Nat := 4983230072969 + 3 ^ 40 * 191471 * 2
def baseEnd_191471 : Nat := 43696290843166934458643

theorem tailTrace_191471 : CollatzResearch.WordTrace tailWord_191471 prefixEnd_191471 43696290843166934458643 := by
  unfold tailWord_191471
  simp only [CollatzResearch.WordTrace]
  refine ⟨6983521089340742488478267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4655680726227161658985511 6983521089340742488478267)
  ·
    refine ⟨10475281634011113732717401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6983521089340742488478267 10475281634011113732717401)
    ·
      refine ⟨7856461225508335299538051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10475281634011113732717401 7856461225508335299538051)
      ·
        refine ⟨11784691838262502949307077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7856461225508335299538051 11784691838262502949307077)
        ·
          refine ⟨2209629719674219302995077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11784691838262502949307077 2209629719674219302995077)
          ·
            refine ⟨414305572438916119311577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2209629719674219302995077 414305572438916119311577)
            ·
              refine ⟨310729179329187089483683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414305572438916119311577 310729179329187089483683)
              ·
                refine ⟨466093768993780634225525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310729179329187089483683 466093768993780634225525)
                ·
                  refine ⟨43696290843166934458643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 466093768993780634225525 43696290843166934458643)
                  ·
                    rfl

theorem cell21_191471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 5].length) (baseStart_191471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_191471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_191471 prefixEnd_191471 := by exact prefixLift 191471
  have htrace : WordTrace (prefixWord ++ tailWord_191471) baseStart_191471 baseEnd_191471 := by
    simpa [prefixWord, tailWord_191471, baseEnd_191471] using wordTrace_append hprefix tailTrace_191471
  have hstable : (prefixWord ++ tailWord_191471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191471).length < 2 ^ (prefixWord ++ tailWord_191471).sum := by decide
  have hdescent : baseEnd_191471 < baseStart_191471 := by decide
  rcases family_descends (prefixWord ++ tailWord_191471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191477 : List Nat := [1, 3, 5, 2, 1, 1, 3, 1, 4]
def baseStart_191477 : Nat := 118140960795 + 191477 * 2 ^ 59
def prefixEnd_191477 : Nat := 4983230072969 + 3 ^ 40 * 191477 * 2
def baseEnd_191477 : Nat := 43697660124912257358631

theorem tailTrace_191477 : CollatzResearch.WordTrace tailWord_191477 prefixEnd_191477 43697660124912257358631 := by
  unfold tailWord_191477
  simp only [CollatzResearch.WordTrace]
  refine ⟨6983739927319005513196685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4655826618212670342131123 6983739927319005513196685)
  ·
    refine ⟨2618902472744627067448757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6983739927319005513196685 2618902472744627067448757)
    ·
      refine ⟨245522106819808787573321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2618902472744627067448757 245522106819808787573321)
      ·
        refine ⟨184141580114856590679991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245522106819808787573321 184141580114856590679991)
        ·
          refine ⟨276212370172284886019987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184141580114856590679991 276212370172284886019987)
          ·
            refine ⟨414318555258427329029981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276212370172284886019987 414318555258427329029981)
            ·
              refine ⟨155369458221910248386243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 414318555258427329029981 155369458221910248386243)
              ·
                refine ⟨233054187332865372579365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155369458221910248386243 233054187332865372579365)
                ·
                  refine ⟨43697660124912257358631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 233054187332865372579365 43697660124912257358631)
                  ·
                    rfl

theorem cell21_191477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_191477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_191477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_191477 prefixEnd_191477 := by exact prefixLift 191477
  have htrace : WordTrace (prefixWord ++ tailWord_191477) baseStart_191477 baseEnd_191477 := by
    simpa [prefixWord, tailWord_191477, baseEnd_191477] using wordTrace_append hprefix tailTrace_191477
  have hstable : (prefixWord ++ tailWord_191477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191477).length < 2 ^ (prefixWord ++ tailWord_191477).sum := by decide
  have hdescent : baseEnd_191477 < baseStart_191477 := by decide
  rcases family_descends (prefixWord ++ tailWord_191477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191609 : List Nat := [1, 2, 1, 3, 5, 1, 3, 5]
def baseStart_191609 : Nat := 118140960795 + 191609 * 2 ^ 59
def prefixEnd_191609 : Nat := 4983230072969 + 3 ^ 40 * 191609 * 2
def baseEnd_191609 : Nat := 14575928107769787052787

theorem tailTrace_191609 : CollatzResearch.WordTrace tailWord_191609 prefixEnd_191609 14575928107769787052787 := by
  unfold tailWord_191609
  simp only [CollatzResearch.WordTrace]
  refine ⟨6988554362840792057001881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4659036241893861371334587 6988554362840792057001881)
  ·
    refine ⟨5241415772130594042751411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6988554362840792057001881 5241415772130594042751411)
    ·
      refine ⟨7862123658195891064127117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5241415772130594042751411 7862123658195891064127117)
      ·
        refine ⟨2948296371823459149047669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7862123658195891064127117 2948296371823459149047669)
        ·
          refine ⟨276402784858449295223219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2948296371823459149047669 276402784858449295223219)
          ·
            refine ⟨414604177287673942834829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276402784858449295223219 414604177287673942834829)
            ·
              refine ⟨155476566482877728563061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 414604177287673942834829 155476566482877728563061)
              ·
                refine ⟨14575928107769787052787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 155476566482877728563061 14575928107769787052787)
                ·
                  rfl

theorem cell21_191609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 5].length) (baseStart_191609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_191609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_191609 prefixEnd_191609 := by exact prefixLift 191609
  have htrace : WordTrace (prefixWord ++ tailWord_191609) baseStart_191609 baseEnd_191609 := by
    simpa [prefixWord, tailWord_191609, baseEnd_191609] using wordTrace_append hprefix tailTrace_191609
  have hstable : (prefixWord ++ tailWord_191609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191609).length < 2 ^ (prefixWord ++ tailWord_191609).sum := by decide
  have hdescent : baseEnd_191609 < baseStart_191609 := by decide
  rcases family_descends (prefixWord ++ tailWord_191609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191637 : List Nat := [1, 3, 2, 1, 1, 1, 2, 6, 4]
def baseStart_191637 : Nat := 118140960795 + 191637 * 2 ^ 59
def prefixEnd_191637 : Nat := 4983230072969 + 3 ^ 40 * 191637 * 2
def baseEnd_191637 : Nat := 43734174304787534691637

theorem tailTrace_191637 : CollatzResearch.WordTrace tailWord_191637 prefixEnd_191637 43734174304787534691637 := by
  unfold tailWord_191637
  simp only [CollatzResearch.WordTrace]
  refine ⟨6989575606739352839021165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4659717071159568559347443 6989575606739352839021165)
  ·
    refine ⟨2621090852527257314632937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6989575606739352839021165 2621090852527257314632937)
    ·
      refine ⟨1965818139395442985974703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2621090852527257314632937 1965818139395442985974703)
      ·
        refine ⟨2948727209093164478962055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1965818139395442985974703 2948727209093164478962055)
        ·
          refine ⟨4423090813639746718443083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2948727209093164478962055 4423090813639746718443083)
          ·
            refine ⟨6634636220459620077664625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4423090813639746718443083 6634636220459620077664625)
            ·
              refine ⟨4975977165344715058248469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6634636220459620077664625 4975977165344715058248469)
              ·
                refine ⟨233248929625533518355397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4975977165344715058248469 233248929625533518355397)
                ·
                  refine ⟨43734174304787534691637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 233248929625533518355397 43734174304787534691637)
                  ·
                    rfl

theorem cell21_191637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_191637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_191637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_191637 prefixEnd_191637 := by exact prefixLift 191637
  have htrace : WordTrace (prefixWord ++ tailWord_191637) baseStart_191637 baseEnd_191637 := by
    simpa [prefixWord, tailWord_191637, baseEnd_191637] using wordTrace_append hprefix tailTrace_191637
  have hstable : (prefixWord ++ tailWord_191637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191637).length < 2 ^ (prefixWord ++ tailWord_191637).sum := by decide
  have hdescent : baseEnd_191637 < baseStart_191637 := by decide
  rcases family_descends (prefixWord ++ tailWord_191637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191640 : List Nat := [2, 1, 2, 4, 2, 1, 2, 4, 3]
def baseStart_191640 : Nat := 118140960795 + 191640 * 2 ^ 59
def prefixEnd_191640 : Nat := 4983230072969 + 3 ^ 40 * 191640 * 2
def baseEnd_191640 : Nat := 43734858945660196141631

theorem tailTrace_191640 : CollatzResearch.WordTrace tailWord_191640 prefixEnd_191640 43734858945660196141631 := by
  unfold tailWord_191640
  simp only [CollatzResearch.WordTrace]
  refine ⟨3494842512864242175690187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4659790017152322900920249 3494842512864242175690187)
  ·
    refine ⟨5242263769296363263535281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3494842512864242175690187 5242263769296363263535281)
    ·
      refine ⟨3931697826972272447651461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5242263769296363263535281 3931697826972272447651461)
      ·
        refine ⟨737193342557301083934649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3931697826972272447651461 737193342557301083934649)
        ·
          refine ⟨552895006917975812950987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 737193342557301083934649 552895006917975812950987)
          ·
            refine ⟨829342510376963719426481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552895006917975812950987 829342510376963719426481)
            ·
              refine ⟨622006882782722789569861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 829342510376963719426481 622006882782722789569861)
              ·
                refine ⟨116626290521760523044349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 622006882782722789569861 116626290521760523044349)
                ·
                  refine ⟨43734858945660196141631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116626290521760523044349 43734858945660196141631)
                  ·
                    rfl

theorem cell21_191640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4, 3].length) (baseStart_191640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_191640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_191640 prefixEnd_191640 := by exact prefixLift 191640
  have htrace : WordTrace (prefixWord ++ tailWord_191640) baseStart_191640 baseEnd_191640 := by
    simpa [prefixWord, tailWord_191640, baseEnd_191640] using wordTrace_append hprefix tailTrace_191640
  have hstable : (prefixWord ++ tailWord_191640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191640).length < 2 ^ (prefixWord ++ tailWord_191640).sum := by decide
  have hdescent : baseEnd_191640 < baseStart_191640 := by decide
  rcases family_descends (prefixWord ++ tailWord_191640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191702 : List Nat := [5, 2, 1, 2, 2, 1, 2, 6]
def baseStart_191702 : Nat := 118140960795 + 191702 * 2 ^ 59
def prefixEnd_191702 : Nat := 4983230072969 + 3 ^ 40 * 191702 * 2
def baseEnd_191702 : Nat := 14583002730120622036057

theorem tailTrace_191702 : CollatzResearch.WordTrace tailWord_191702 prefixEnd_191702 14583002730120622036057 := by
  unfold tailWord_191702
  simp only [CollatzResearch.WordTrace]
  refine ⟨436996646968991808758585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4661297567669245960091573 436996646968991808758585)
  ·
    refine ⟨327747485226743856568939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 436996646968991808758585 327747485226743856568939)
    ·
      refine ⟨491621227840115784853409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327747485226743856568939 491621227840115784853409)
      ·
        refine ⟨368715920880086838640057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 491621227840115784853409 368715920880086838640057)
        ·
          refine ⟨276536940660065128980043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368715920880086838640057 276536940660065128980043)
          ·
            refine ⟨414805410990097693470065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276536940660065128980043 414805410990097693470065)
            ·
              refine ⟨311104058242573270102549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414805410990097693470065 311104058242573270102549)
              ·
                refine ⟨14583002730120622036057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 311104058242573270102549 14583002730120622036057)
                ·
                  rfl

theorem cell21_191702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_191702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_191702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_191702 prefixEnd_191702 := by exact prefixLift 191702
  have htrace : WordTrace (prefixWord ++ tailWord_191702) baseStart_191702 baseEnd_191702 := by
    simpa [prefixWord, tailWord_191702, baseEnd_191702] using wordTrace_append hprefix tailTrace_191702
  have hstable : (prefixWord ++ tailWord_191702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191702).length < 2 ^ (prefixWord ++ tailWord_191702).sum := by decide
  have hdescent : baseEnd_191702 < baseStart_191702 := by decide
  rcases family_descends (prefixWord ++ tailWord_191702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191775 : List Nat := [1, 1, 2, 4, 4, 1, 1, 2, 5]
def baseStart_191775 : Nat := 118140960795 + 191775 * 2 ^ 59
def prefixEnd_191775 : Nat := 4983230072969 + 3 ^ 40 * 191775 * 2
def baseEnd_191775 : Nat := 43765667784929961391355

theorem tailTrace_191775 : CollatzResearch.WordTrace tailWord_191775 prefixEnd_191775 43765667784929961391355 := by
  unfold tailWord_191775
  simp only [CollatzResearch.WordTrace]
  refine ⟨6994608880239402407544779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4663072586826268271696519 6994608880239402407544779)
  ·
    refine ⟨10491913320359103611317169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6994608880239402407544779 10491913320359103611317169)
    ·
      refine ⟨7868934990269327708487877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10491913320359103611317169 7868934990269327708487877)
      ·
        refine ⟨1475425310675498945341477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7868934990269327708487877 1475425310675498945341477)
        ·
          refine ⟨276642245751656052251527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1475425310675498945341477 276642245751656052251527)
          ·
            refine ⟨414963368627484078377291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276642245751656052251527 414963368627484078377291)
            ·
              refine ⟨622445052941226117565937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414963368627484078377291 622445052941226117565937)
              ·
                refine ⟨466833789705919588174453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 622445052941226117565937 466833789705919588174453)
                ·
                  refine ⟨43765667784929961391355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 466833789705919588174453 43765667784929961391355)
                  ·
                    rfl

theorem cell21_191775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 5].length) (baseStart_191775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_191775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_191775 prefixEnd_191775 := by exact prefixLift 191775
  have htrace : WordTrace (prefixWord ++ tailWord_191775) baseStart_191775 baseEnd_191775 := by
    simpa [prefixWord, tailWord_191775, baseEnd_191775] using wordTrace_append hprefix tailTrace_191775
  have hstable : (prefixWord ++ tailWord_191775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191775).length < 2 ^ (prefixWord ++ tailWord_191775).sum := by decide
  have hdescent : baseEnd_191775 < baseStart_191775 := by decide
  rcases family_descends (prefixWord ++ tailWord_191775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191834 : List Nat := [3, 1, 1, 2, 1, 2, 4, 2, 5]
def baseStart_191834 : Nat := 118140960795 + 191834 * 2 ^ 59
def prefixEnd_191834 : Nat := 4983230072969 + 3 ^ 40 * 191834 * 2
def baseEnd_191834 : Nat := 43779132388758969907901

theorem tailTrace_191834 : CollatzResearch.WordTrace tailWord_191834 prefixEnd_191834 43779132388758969907901 := by
  unfold tailWord_191834
  simp only [CollatzResearch.WordTrace]
  refine ⟨1749190196756413870985639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4664507191350436989295037 1749190196756413870985639)
  ·
    refine ⟨2623785295134620806478459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1749190196756413870985639 2623785295134620806478459)
    ·
      refine ⟨3935677942701931209717689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2623785295134620806478459 3935677942701931209717689)
      ·
        refine ⟨2951758457026448407288267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3935677942701931209717689 2951758457026448407288267)
        ·
          refine ⟨4427637685539672610932401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2951758457026448407288267 4427637685539672610932401)
          ·
            refine ⟨3320728264154754458199301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4427637685539672610932401 3320728264154754458199301)
            ·
              refine ⟨622636549529016460912369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3320728264154754458199301 622636549529016460912369)
              ·
                refine ⟨466977412146762345684277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 622636549529016460912369 466977412146762345684277)
                ·
                  refine ⟨43779132388758969907901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 466977412146762345684277 43779132388758969907901)
                  ·
                    rfl

theorem cell21_191834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_191834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_191834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_191834 prefixEnd_191834 := by exact prefixLift 191834
  have htrace : WordTrace (prefixWord ++ tailWord_191834) baseStart_191834 baseEnd_191834 := by
    simpa [prefixWord, tailWord_191834, baseEnd_191834] using wordTrace_append hprefix tailTrace_191834
  have hstable : (prefixWord ++ tailWord_191834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191834).length < 2 ^ (prefixWord ++ tailWord_191834).sum := by decide
  have hdescent : baseEnd_191834 < baseStart_191834 := by decide
  rcases family_descends (prefixWord ++ tailWord_191834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191854 : List Nat := [4, 1, 2, 4, 2, 1, 7]
def baseStart_191854 : Nat := 118140960795 + 191854 * 2 ^ 59
def prefixEnd_191854 : Nat := 4983230072969 + 3 ^ 40 * 191854 * 2
def baseEnd_191854 : Nat := 4864855184582597730503

theorem tailTrace_191854 : CollatzResearch.WordTrace tailWord_191854 prefixEnd_191854 4864855184582597730503 := by
  unfold tailWord_191854
  simp only [CollatzResearch.WordTrace]
  refine ⟨874686280869149862458827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4664993497968799266447077 874686280869149862458827)
  ·
    refine ⟨1312029421303724793688241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 874686280869149862458827 1312029421303724793688241)
    ·
      refine ⟨984022065977793595266181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1312029421303724793688241 984022065977793595266181)
      ·
        refine ⟨184504137370836299112409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 984022065977793595266181 184504137370836299112409)
        ·
          refine ⟨138378103028127224334307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184504137370836299112409 138378103028127224334307)
          ·
            refine ⟨207567154542190836501461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138378103028127224334307 207567154542190836501461)
            ·
              refine ⟨4864855184582597730503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 207567154542190836501461 4864855184582597730503)
              ·
                rfl

theorem cell21_191854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 7].length) (baseStart_191854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_191854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_191854 prefixEnd_191854 := by exact prefixLift 191854
  have htrace : WordTrace (prefixWord ++ tailWord_191854) baseStart_191854 baseEnd_191854 := by
    simpa [prefixWord, tailWord_191854, baseEnd_191854] using wordTrace_append hprefix tailTrace_191854
  have hstable : (prefixWord ++ tailWord_191854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191854).length < 2 ^ (prefixWord ++ tailWord_191854).sum := by decide
  have hdescent : baseEnd_191854 < baseStart_191854 := by decide
  rcases family_descends (prefixWord ++ tailWord_191854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191868 : List Nat := [2, 2, 2, 1, 1, 1, 7, 2, 3]
def baseStart_191868 : Nat := 118140960795 + 191868 * 2 ^ 59
def prefixEnd_191868 : Nat := 4983230072969 + 3 ^ 40 * 191868 * 2
def baseEnd_191868 : Nat := 43786891651982466341165

theorem tailTrace_191868 : CollatzResearch.WordTrace tailWord_191868 prefixEnd_191868 43786891651982466341165 := by
  unfold tailWord_191868
  simp only [CollatzResearch.WordTrace]
  refine ⟨3499000434451239645340129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4665333912601652860453505 3499000434451239645340129)
  ·
    refine ⟨2624250325838429734005097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3499000434451239645340129 2624250325838429734005097)
    ·
      refine ⟨1968187744378822300503823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2624250325838429734005097 1968187744378822300503823)
      ·
        refine ⟨2952281616568233450755735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1968187744378822300503823 2952281616568233450755735)
        ·
          refine ⟨4428422424852350176133603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2952281616568233450755735 4428422424852350176133603)
          ·
            refine ⟨6642633637278525264200405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4428422424852350176133603 6642633637278525264200405)
            ·
              refine ⟨155686725873715435879697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 6642633637278525264200405 155686725873715435879697)
              ·
                refine ⟨116765044405286576909773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155686725873715435879697 116765044405286576909773)
                ·
                  refine ⟨43786891651982466341165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116765044405286576909773 43786891651982466341165)
                  ·
                    rfl

theorem cell21_191868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2, 3].length) (baseStart_191868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_191868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_191868 prefixEnd_191868 := by exact prefixLift 191868
  have htrace : WordTrace (prefixWord ++ tailWord_191868) baseStart_191868 baseEnd_191868 := by
    simpa [prefixWord, tailWord_191868, baseEnd_191868] using wordTrace_append hprefix tailTrace_191868
  have hstable : (prefixWord ++ tailWord_191868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191868).length < 2 ^ (prefixWord ++ tailWord_191868).sum := by decide
  have hdescent : baseEnd_191868 < baseStart_191868 := by decide
  rcases family_descends (prefixWord ++ tailWord_191868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191879 : List Nat := [1, 1, 4, 2, 2, 2, 1, 8]
def baseStart_191879 : Nat := 118140960795 + 191879 * 2 ^ 59
def prefixEnd_191879 : Nat := 4983230072969 + 3 ^ 40 * 191879 * 2
def baseEnd_191879 : Nat := 14596467333949630552603

theorem tailTrace_191879 : CollatzResearch.WordTrace tailWord_191879 prefixEnd_191879 14596467333949630552603 := by
  unfold tailWord_191879
  simp only [CollatzResearch.WordTrace]
  refine ⟨6998402071862628169330691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4665601381241752112887127 6998402071862628169330691)
  ·
    refine ⟨10497603107793942253996037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6998402071862628169330691 10497603107793942253996037)
    ·
      refine ⟨1968300582711364172624257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10497603107793942253996037 1968300582711364172624257)
      ·
        refine ⟨1476225437033523129468193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1968300582711364172624257 1476225437033523129468193)
        ·
          refine ⟨1107169077775142347101145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1476225437033523129468193 1107169077775142347101145)
          ·
            refine ⟨830376808331356760325859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1107169077775142347101145 830376808331356760325859)
            ·
              refine ⟨1245565212497035140488789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 830376808331356760325859 1245565212497035140488789)
              ·
                refine ⟨14596467333949630552603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1245565212497035140488789 14596467333949630552603)
                ·
                  rfl

theorem cell21_191879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 8].length) (baseStart_191879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_191879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_191879 prefixEnd_191879 := by exact prefixLift 191879
  have htrace : WordTrace (prefixWord ++ tailWord_191879) baseStart_191879 baseEnd_191879 := by
    simpa [prefixWord, tailWord_191879, baseEnd_191879] using wordTrace_append hprefix tailTrace_191879
  have hstable : (prefixWord ++ tailWord_191879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191879).length < 2 ^ (prefixWord ++ tailWord_191879).sum := by decide
  have hdescent : baseEnd_191879 < baseStart_191879 := by decide
  rcases family_descends (prefixWord ++ tailWord_191879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191927 : List Nat := [1, 1, 3, 1, 3, 2, 3, 4, 3]
def baseStart_191927 : Nat := 118140960795 + 191927 * 2 ^ 59
def prefixEnd_191927 : Nat := 4983230072969 + 3 ^ 40 * 191927 * 2
def baseEnd_191927 : Nat := 43800356255811474857711

theorem tailTrace_191927 : CollatzResearch.WordTrace tailWord_191927 prefixEnd_191927 43800356255811474857711 := by
  unfold tailWord_191927
  simp only [CollatzResearch.WordTrace]
  refine ⟨7000152775688732367078035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4666768517125821578052023 7000152775688732367078035)
  ·
    refine ⟨10500229163533098550617053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7000152775688732367078035 10500229163533098550617053)
    ·
      refine ⟨3937585936324911956481395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10500229163533098550617053 3937585936324911956481395)
      ·
        refine ⟨5906378904487367934722093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3937585936324911956481395 5906378904487367934722093)
        ·
          refine ⟨2214892089182762975520785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5906378904487367934722093 2214892089182762975520785)
          ·
            refine ⟨1661169066887072231640589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2214892089182762975520785 1661169066887072231640589)
            ·
              refine ⟨622938400082652086865221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1661169066887072231640589 622938400082652086865221)
              ·
                refine ⟨116800950015497266287229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 622938400082652086865221 116800950015497266287229)
                ·
                  refine ⟨43800356255811474857711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116800950015497266287229 43800356255811474857711)
                  ·
                    rfl

theorem cell21_191927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 3].length) (baseStart_191927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_191927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_191927 prefixEnd_191927 := by exact prefixLift 191927
  have htrace : WordTrace (prefixWord ++ tailWord_191927) baseStart_191927 baseEnd_191927 := by
    simpa [prefixWord, tailWord_191927, baseEnd_191927] using wordTrace_append hprefix tailTrace_191927
  have hstable : (prefixWord ++ tailWord_191927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191927).length < 2 ^ (prefixWord ++ tailWord_191927).sum := by decide
  have hdescent : baseEnd_191927 < baseStart_191927 := by decide
  rcases family_descends (prefixWord ++ tailWord_191927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192183 : List Nat := [1, 1, 3, 1, 5, 2, 1, 7]
def baseStart_192183 : Nat := 118140960795 + 192183 * 2 ^ 59
def prefixEnd_192183 : Nat := 4983230072969 + 3 ^ 40 * 192183 * 2
def baseEnd_192183 : Nat := 14619592981203972863507

theorem tailTrace_192183 : CollatzResearch.WordTrace tailWord_192183 prefixEnd_192183 14619592981203972863507 := by
  unfold tailWord_192183
  simp only [CollatzResearch.WordTrace]
  refine ⟨7009489862761288088397203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4672993241840858725598135 7009489862761288088397203)
  ·
    refine ⟨10514234794141932132595805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7009489862761288088397203 10514234794141932132595805)
    ·
      refine ⟨3942838047803224549723427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10514234794141932132595805 3942838047803224549723427)
      ·
        refine ⟨5914257071704836824585141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3942838047803224549723427 5914257071704836824585141)
        ·
          refine ⟨554461600472328452304857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5914257071704836824585141 554461600472328452304857)
          ·
            refine ⟨415846200354246339228643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 554461600472328452304857 415846200354246339228643)
            ·
              refine ⟨623769300531369508842965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415846200354246339228643 623769300531369508842965)
              ·
                refine ⟨14619592981203972863507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 623769300531369508842965 14619592981203972863507)
                ·
                  rfl

theorem cell21_192183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 7].length) (baseStart_192183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_192183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_192183 prefixEnd_192183 := by exact prefixLift 192183
  have htrace : WordTrace (prefixWord ++ tailWord_192183) baseStart_192183 baseEnd_192183 := by
    simpa [prefixWord, tailWord_192183, baseEnd_192183] using wordTrace_append hprefix tailTrace_192183
  have hstable : (prefixWord ++ tailWord_192183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192183).length < 2 ^ (prefixWord ++ tailWord_192183).sum := by decide
  have hdescent : baseEnd_192183 < baseStart_192183 := by decide
  rcases family_descends (prefixWord ++ tailWord_192183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192220 : List Nat := [2, 2, 5, 1, 2, 2, 2, 1, 4]
def baseStart_192220 : Nat := 118140960795 + 192220 * 2 ^ 59
def prefixEnd_192220 : Nat := 4983230072969 + 3 ^ 40 * 192220 * 2
def baseEnd_192220 : Nat := 43867222847708076473779

theorem tailTrace_192220 : CollatzResearch.WordTrace tailWord_192220 prefixEnd_192220 43867222847708076473779 := by
  unfold tailWord_192220
  simp only [CollatzResearch.WordTrace]
  refine ⟨3505419681813621703747057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4673892909084828938329409 3505419681813621703747057)
  ·
    refine ⟨2629064761360216277810293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3505419681813621703747057 2629064761360216277810293)
    ·
      refine ⟨246474821377520276044715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2629064761360216277810293 246474821377520276044715)
      ·
        refine ⟨369712232066280414067073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246474821377520276044715 369712232066280414067073)
        ·
          refine ⟨277284174049710310550305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369712232066280414067073 277284174049710310550305)
          ·
            refine ⟨207963130537282732912729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277284174049710310550305 207963130537282732912729)
            ·
              refine ⟨155972347902962049684547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207963130537282732912729 155972347902962049684547)
              ·
                refine ⟨233958521854443074526821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155972347902962049684547 233958521854443074526821)
                ·
                  refine ⟨43867222847708076473779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 233958521854443074526821 43867222847708076473779)
                  ·
                    rfl

theorem cell21_192220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_192220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_192220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_192220 prefixEnd_192220 := by exact prefixLift 192220
  have htrace : WordTrace (prefixWord ++ tailWord_192220) baseStart_192220 baseEnd_192220 := by
    simpa [prefixWord, tailWord_192220, baseEnd_192220] using wordTrace_append hprefix tailTrace_192220
  have hstable : (prefixWord ++ tailWord_192220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192220).length < 2 ^ (prefixWord ++ tailWord_192220).sum := by decide
  have hdescent : baseEnd_192220 < baseStart_192220 := by decide
  rcases family_descends (prefixWord ++ tailWord_192220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192273 : List Nat := [1, 2, 2, 1, 1, 3, 1, 5, 5]
def baseStart_192273 : Nat := 118140960795 + 192273 * 2 ^ 59
def prefixEnd_192273 : Nat := 4983230072969 + 3 ^ 40 * 192273 * 2
def baseEnd_192273 : Nat := 43879318169791762090337

theorem tailTrace_192273 : CollatzResearch.WordTrace tailWord_192273 prefixEnd_192273 43879318169791762090337 := by
  unfold tailWord_192273
  simp only [CollatzResearch.WordTrace]
  refine ⟨7012772432435233459173473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4675181621623488972782315 7012772432435233459173473)
  ·
    refine ⟨5259579324326425094380105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7012772432435233459173473 5259579324326425094380105)
    ·
      refine ⟨3944684493244818820785079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5259579324326425094380105 3944684493244818820785079)
      ·
        refine ⟨5917026739867228231177619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3944684493244818820785079 5917026739867228231177619)
        ·
          refine ⟨8875540109800842346766429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5917026739867228231177619 8875540109800842346766429)
          ·
            refine ⟨3328327541175315880037411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8875540109800842346766429 3328327541175315880037411)
            ·
              refine ⟨4992491311762973820056117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3328327541175315880037411 4992491311762973820056117)
              ·
                refine ⟨468046060477778795630261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4992491311762973820056117 468046060477778795630261)
                ·
                  refine ⟨43879318169791762090337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 468046060477778795630261 43879318169791762090337)
                  ·
                    rfl

theorem cell21_192273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 5].length) (baseStart_192273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_192273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_192273 prefixEnd_192273 := by exact prefixLift 192273
  have htrace : WordTrace (prefixWord ++ tailWord_192273) baseStart_192273 baseEnd_192273 := by
    simpa [prefixWord, tailWord_192273, baseEnd_192273] using wordTrace_append hprefix tailTrace_192273
  have hstable : (prefixWord ++ tailWord_192273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192273).length < 2 ^ (prefixWord ++ tailWord_192273).sum := by decide
  have hdescent : baseEnd_192273 < baseStart_192273 := by decide
  rcases family_descends (prefixWord ++ tailWord_192273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192290 : List Nat := [3, 3, 1, 1, 2, 1, 3, 2, 5]
def baseStart_192290 : Nat := 118140960795 + 192290 * 2 ^ 59
def prefixEnd_192290 : Nat := 4983230072969 + 3 ^ 40 * 192290 * 2
def baseEnd_192290 : Nat := 43883197801403510306969

theorem tailTrace_192290 : CollatzResearch.WordTrace tailWord_192290 prefixEnd_192290 43883197801403510306969 := by
  unfold tailWord_192290
  simp only [CollatzResearch.WordTrace]
  refine ⟨1753348118343411340635581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4675594982249096908361549 1753348118343411340635581)
  ·
    refine ⟨657505544378779252738343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1753348118343411340635581 657505544378779252738343)
    ·
      refine ⟨986258316568168879107515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 657505544378779252738343 986258316568168879107515)
      ·
        refine ⟨1479387474852253318661273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 986258316568168879107515 1479387474852253318661273)
        ·
          refine ⟨1109540606139189988995955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1479387474852253318661273 1109540606139189988995955)
          ·
            refine ⟨1664310909208784983493933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1109540606139189988995955 1664310909208784983493933)
            ·
              refine ⟨624116590953294368810225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1664310909208784983493933 624116590953294368810225)
              ·
                refine ⟨468087443214970776607669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 624116590953294368810225 468087443214970776607669)
                ·
                  refine ⟨43883197801403510306969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 468087443214970776607669 43883197801403510306969)
                  ·
                    rfl

theorem cell21_192290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_192290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_192290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_192290 prefixEnd_192290 := by exact prefixLift 192290
  have htrace : WordTrace (prefixWord ++ tailWord_192290) baseStart_192290 baseEnd_192290 := by
    simpa [prefixWord, tailWord_192290, baseEnd_192290] using wordTrace_append hprefix tailTrace_192290
  have hstable : (prefixWord ++ tailWord_192290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192290).length < 2 ^ (prefixWord ++ tailWord_192290).sum := by decide
  have hdescent : baseEnd_192290 < baseStart_192290 := by decide
  rcases family_descends (prefixWord ++ tailWord_192290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192338 : List Nat := [3, 2, 2, 1, 1, 4, 3, 1, 4]
def baseStart_192338 : Nat := 118140960795 + 192338 * 2 ^ 59
def prefixEnd_192338 : Nat := 4983230072969 + 3 ^ 40 * 192338 * 2
def baseEnd_192338 : Nat := 43894152055366093506871

theorem tailTrace_192338 : CollatzResearch.WordTrace tailWord_192338 prefixEnd_192338 43894152055366093506871 := by
  unfold tailWord_192338
  simp only [CollatzResearch.WordTrace]
  refine ⟨1753785794299937390072417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4676762118133166373526445 1753785794299937390072417)
  ·
    refine ⟨1315339345724953042554313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1753785794299937390072417 1315339345724953042554313)
    ·
      refine ⟨986504509293714781915735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1315339345724953042554313 986504509293714781915735)
      ·
        refine ⟨1479756763940572172873603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 986504509293714781915735 1479756763940572172873603)
        ·
          refine ⟨2219635145910858259310405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1479756763940572172873603 2219635145910858259310405)
          ·
            refine ⟨416181589858285923620701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2219635145910858259310405 416181589858285923620701)
            ·
              refine ⟨156068096196857221357763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 416181589858285923620701 156068096196857221357763)
              ·
                refine ⟨234102144295285832036645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156068096196857221357763 234102144295285832036645)
                ·
                  refine ⟨43894152055366093506871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 234102144295285832036645 43894152055366093506871)
                  ·
                    rfl

theorem cell21_192338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_192338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_192338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_192338 prefixEnd_192338 := by exact prefixLift 192338
  have htrace : WordTrace (prefixWord ++ tailWord_192338) baseStart_192338 baseEnd_192338 := by
    simpa [prefixWord, tailWord_192338, baseEnd_192338] using wordTrace_append hprefix tailTrace_192338
  have hstable : (prefixWord ++ tailWord_192338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192338).length < 2 ^ (prefixWord ++ tailWord_192338).sum := by decide
  have hdescent : baseEnd_192338 < baseStart_192338 := by decide
  rcases family_descends (prefixWord ++ tailWord_192338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192352 : List Nat := [2, 1, 1, 3, 3, 4, 2, 5]
def baseStart_192352 : Nat := 118140960795 + 192352 * 2 ^ 59
def prefixEnd_192352 : Nat := 4983230072969 + 3 ^ 40 * 192352 * 2
def baseEnd_192352 : Nat := 14632449015368393424503

theorem tailTrace_192352 : CollatzResearch.WordTrace tailWord_192352 prefixEnd_192352 14632449015368393424503 := by
  unfold tailWord_192352
  simp only [CollatzResearch.WordTrace]
  refine ⟨3507826899574514975649655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4677102532766019967532873 3507826899574514975649655)
  ·
    refine ⟨5261740349361772463474483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3507826899574514975649655 5261740349361772463474483)
    ·
      refine ⟨7892610524042658695211725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5261740349361772463474483 7892610524042658695211725)
      ·
        refine ⟨2959728946515997010704397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7892610524042658695211725 2959728946515997010704397)
        ·
          refine ⟨1109898354943498879014149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2959728946515997010704397 1109898354943498879014149)
          ·
            refine ⟨208105941551906039815153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1109898354943498879014149 208105941551906039815153)
            ·
              refine ⟨156079456163929529861365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208105941551906039815153 156079456163929529861365)
              ·
                refine ⟨14632449015368393424503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156079456163929529861365 14632449015368393424503)
                ·
                  rfl

theorem cell21_192352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 5].length) (baseStart_192352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_192352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_192352 prefixEnd_192352 := by exact prefixLift 192352
  have htrace : WordTrace (prefixWord ++ tailWord_192352) baseStart_192352 baseEnd_192352 := by
    simpa [prefixWord, tailWord_192352, baseEnd_192352] using wordTrace_append hprefix tailTrace_192352
  have hstable : (prefixWord ++ tailWord_192352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192352).length < 2 ^ (prefixWord ++ tailWord_192352).sum := by decide
  have hdescent : baseEnd_192352 < baseStart_192352 := by decide
  rcases family_descends (prefixWord ++ tailWord_192352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192487 : List Nat := [1, 1, 5, 2, 3, 1, 8]
def baseStart_192487 : Nat := 118140960795 + 192487 * 2 ^ 59
def prefixEnd_192487 : Nat := 4983230072969 + 3 ^ 40 * 192487 * 2
def baseEnd_192487 : Nat := 4880906209486105058137

theorem tailTrace_192487 : CollatzResearch.WordTrace tailWord_192487 prefixEnd_192487 4880906209486105058137 := by
  unfold tailWord_192487
  simp only [CollatzResearch.WordTrace]
  refine ⟨7020577653659948007463715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4680385102439965338309143 7020577653659948007463715)
  ·
    refine ⟨10530866480489922011195573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7020577653659948007463715 10530866480489922011195573)
    ·
      refine ⟨987268732545930188549585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10530866480489922011195573 987268732545930188549585)
      ·
        refine ⟨740451549409447641412189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 987268732545930188549585 740451549409447641412189)
        ·
          refine ⟨277669331028542865529571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 740451549409447641412189 277669331028542865529571)
          ·
            refine ⟨416503996542814298294357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277669331028542865529571 416503996542814298294357)
            ·
              refine ⟨4880906209486105058137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 416503996542814298294357 4880906209486105058137)
              ·
                rfl

theorem cell21_192487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 8].length) (baseStart_192487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_192487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_192487 prefixEnd_192487 := by exact prefixLift 192487
  have htrace : WordTrace (prefixWord ++ tailWord_192487) baseStart_192487 baseEnd_192487 := by
    simpa [prefixWord, tailWord_192487, baseEnd_192487] using wordTrace_append hprefix tailTrace_192487
  have hstable : (prefixWord ++ tailWord_192487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192487).length < 2 ^ (prefixWord ++ tailWord_192487).sum := by decide
  have hdescent : baseEnd_192487 < baseStart_192487 := by decide
  rcases family_descends (prefixWord ++ tailWord_192487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192552 : List Nat := [2, 1, 5, 3, 1, 2, 1, 1, 5]
def baseStart_192552 : Nat := 118140960795 + 192552 * 2 ^ 59
def prefixEnd_192552 : Nat := 4983230072969 + 3 ^ 40 * 192552 * 2
def baseEnd_192552 : Nat := 43942989770949276939767

theorem tailTrace_192552 : CollatzResearch.WordTrace tailWord_192552 prefixEnd_192552 43942989770949276939767 := by
  unfold tailWord_192552
  simp only [CollatzResearch.WordTrace]
  refine ⟨3511474199212232054289955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4681965598949642739053273 3511474199212232054289955)
  ·
    refine ⟨5267211298818348081434933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3511474199212232054289955 5267211298818348081434933)
    ·
      refine ⟨493801059264220132634525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5267211298818348081434933 493801059264220132634525)
      ·
        refine ⟨185175397224082549737947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 493801059264220132634525 185175397224082549737947)
        ·
          refine ⟨277763095836123824606921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185175397224082549737947 277763095836123824606921)
          ·
            refine ⟨208322321877092868455191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277763095836123824606921 208322321877092868455191)
            ·
              refine ⟨312483482815639302682787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208322321877092868455191 312483482815639302682787)
              ·
                refine ⟨468725224223458954024181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312483482815639302682787 468725224223458954024181)
                ·
                  refine ⟨43942989770949276939767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 468725224223458954024181 43942989770949276939767)
                  ·
                    rfl

theorem cell21_192552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 5].length) (baseStart_192552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_192552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_192552 prefixEnd_192552 := by exact prefixLift 192552
  have htrace : WordTrace (prefixWord ++ tailWord_192552) baseStart_192552 baseEnd_192552 := by
    simpa [prefixWord, tailWord_192552, baseEnd_192552] using wordTrace_append hprefix tailTrace_192552
  have hstable : (prefixWord ++ tailWord_192552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192552).length < 2 ^ (prefixWord ++ tailWord_192552).sum := by decide
  have hdescent : baseEnd_192552 < baseStart_192552 := by decide
  rcases family_descends (prefixWord ++ tailWord_192552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192608 : List Nat := [2, 1, 1, 3, 2, 3, 1, 4, 4]
def baseStart_192608 : Nat := 118140960795 + 192608 * 2 ^ 59
def prefixEnd_192608 : Nat := 4983230072969 + 3 ^ 40 * 192608 * 2
def baseEnd_192608 : Nat := 43955769733905624006319

theorem tailTrace_192608 : CollatzResearch.WordTrace tailWord_192608 prefixEnd_192608 43955769733905624006319 := by
  unfold tailWord_192608
  simp only [CollatzResearch.WordTrace]
  refine ⟨3512495443110792836309239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4683327257481057115078985 3512495443110792836309239)
  ·
    refine ⟨5268743164666189254463859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3512495443110792836309239 5268743164666189254463859)
    ·
      refine ⟨7903114746999283881695789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5268743164666189254463859 7903114746999283881695789)
      ·
        refine ⟨2963668030124731455635921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7903114746999283881695789 2963668030124731455635921)
        ·
          refine ⟨2222751022593548591726941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2963668030124731455635921 2222751022593548591726941)
          ·
            refine ⟨833531633472580721897603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2222751022593548591726941 833531633472580721897603)
            ·
              refine ⟨1250297450208871082846405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833531633472580721897603 1250297450208871082846405)
              ·
                refine ⟨234430771914163328033701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1250297450208871082846405 234430771914163328033701)
                ·
                  refine ⟨43955769733905624006319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 234430771914163328033701 43955769733905624006319)
                  ·
                    rfl

theorem cell21_192608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 4].length) (baseStart_192608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_192608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_192608 prefixEnd_192608 := by exact prefixLift 192608
  have htrace : WordTrace (prefixWord ++ tailWord_192608) baseStart_192608 baseEnd_192608 := by
    simpa [prefixWord, tailWord_192608, baseEnd_192608] using wordTrace_append hprefix tailTrace_192608
  have hstable : (prefixWord ++ tailWord_192608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192608).length < 2 ^ (prefixWord ++ tailWord_192608).sum := by decide
  have hdescent : baseEnd_192608 < baseStart_192608 := by decide
  rcases family_descends (prefixWord ++ tailWord_192608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192611 : List Nat := [1, 1, 1, 5, 1, 1, 6, 2, 3]
def baseStart_192611 : Nat := 118140960795 + 192611 * 2 ^ 59
def prefixEnd_192611 : Nat := 4983230072969 + 3 ^ 40 * 192611 * 2
def baseEnd_192611 : Nat := 43956454374778285456313

theorem tailTrace_192611 : CollatzResearch.WordTrace tailWord_192611 prefixEnd_192611 43956454374778285456313 := by
  unfold tailWord_192611
  simp only [CollatzResearch.WordTrace]
  refine ⟨7025100305210717184977687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4683400203473811456651791 7025100305210717184977687)
  ·
    refine ⟨10537650457816075777466531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7025100305210717184977687 10537650457816075777466531)
    ·
      refine ⟨15806475686724113666199797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10537650457816075777466531 15806475686724113666199797)
      ·
        refine ⟨1481857095630385656206231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15806475686724113666199797 1481857095630385656206231)
        ·
          refine ⟨2222785643445578484309347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1481857095630385656206231 2222785643445578484309347)
          ·
            refine ⟨3334178465168367726464021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2222785643445578484309347 3334178465168367726464021)
            ·
              refine ⟨156289615554767237178001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3334178465168367726464021 156289615554767237178001)
              ·
                refine ⟨117217211666075427883501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156289615554767237178001 117217211666075427883501)
                ·
                  refine ⟨43956454374778285456313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117217211666075427883501 43956454374778285456313)
                  ·
                    rfl

theorem cell21_192611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2, 3].length) (baseStart_192611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_192611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_192611 prefixEnd_192611 := by exact prefixLift 192611
  have htrace : WordTrace (prefixWord ++ tailWord_192611) baseStart_192611 baseEnd_192611 := by
    simpa [prefixWord, tailWord_192611, baseEnd_192611] using wordTrace_append hprefix tailTrace_192611
  have hstable : (prefixWord ++ tailWord_192611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192611).length < 2 ^ (prefixWord ++ tailWord_192611).sum := by decide
  have hdescent : baseEnd_192611 < baseStart_192611 := by decide
  rcases family_descends (prefixWord ++ tailWord_192611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192662 : List Nat := [5, 3, 2, 1, 1, 1, 2, 1, 5]
def baseStart_192662 : Nat := 118140960795 + 192662 * 2 ^ 59
def prefixEnd_192662 : Nat := 4983230072969 + 3 ^ 40 * 192662 * 2
def baseEnd_192662 : Nat := 43968093269613530106209

theorem tailTrace_192662 : CollatzResearch.WordTrace tailWord_192662 prefixEnd_192662 43968093269613530106209 := by
  unfold tailWord_192662
  simp only [CollatzResearch.WordTrace]
  refine ⟨439185026751622055942765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4684640285350635263389493 439185026751622055942765)
  ·
    refine ⟨164694385031858270978537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 439185026751622055942765 164694385031858270978537)
    ·
      refine ⟨123520788773893703233903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164694385031858270978537 123520788773893703233903)
      ·
        refine ⟨185281183160840554850855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123520788773893703233903 185281183160840554850855)
        ·
          refine ⟨277921774741260832276283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185281183160840554850855 277921774741260832276283)
          ·
            refine ⟨416882662111891248414425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277921774741260832276283 416882662111891248414425)
            ·
              refine ⟨312661996583918436310819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416882662111891248414425 312661996583918436310819)
              ·
                refine ⟨468992994875877654466229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312661996583918436310819 468992994875877654466229)
                ·
                  refine ⟨43968093269613530106209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 468992994875877654466229 43968093269613530106209)
                  ·
                    rfl

theorem cell21_192662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_192662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_192662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_192662 prefixEnd_192662 := by exact prefixLift 192662
  have htrace : WordTrace (prefixWord ++ tailWord_192662) baseStart_192662 baseEnd_192662 := by
    simpa [prefixWord, tailWord_192662, baseEnd_192662] using wordTrace_append hprefix tailTrace_192662
  have hstable : (prefixWord ++ tailWord_192662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192662).length < 2 ^ (prefixWord ++ tailWord_192662).sum := by decide
  have hdescent : baseEnd_192662 < baseStart_192662 := by decide
  rcases family_descends (prefixWord ++ tailWord_192662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192729 : List Nat := [1, 2, 1, 2, 3, 1, 5, 1, 5]
def baseStart_192729 : Nat := 118140960795 + 192729 * 2 ^ 59
def prefixEnd_192729 : Nat := 4983230072969 + 3 ^ 40 * 192729 * 2
def baseEnd_192729 : Nat := 43983383582436302489405

theorem tailTrace_192729 : CollatzResearch.WordTrace tailWord_192729 prefixEnd_192729 43983383582436302489405 := by
  unfold tailWord_192729
  simp only [CollatzResearch.WordTrace]
  refine ⟨7029404118783223337773241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4686269412522148891848827 7029404118783223337773241)
  ·
    refine ⟨5272053089087417503329931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7029404118783223337773241 5272053089087417503329931)
    ·
      refine ⟨7908079633631126254994897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5272053089087417503329931 7908079633631126254994897)
      ·
        refine ⟨5931059725223344691246173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7908079633631126254994897 5931059725223344691246173)
        ·
          refine ⟨2224147396958754259217315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5931059725223344691246173 2224147396958754259217315)
          ·
            refine ⟨3336221095438131388825973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2224147396958754259217315 3336221095438131388825973)
            ·
              refine ⟨312770727697324817702435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3336221095438131388825973 312770727697324817702435)
              ·
                refine ⟨469156091545987226553653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312770727697324817702435 469156091545987226553653)
                ·
                  refine ⟨43983383582436302489405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 469156091545987226553653 43983383582436302489405)
                  ·
                    rfl

theorem cell21_192729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 5].length) (baseStart_192729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_192729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_192729 prefixEnd_192729 := by exact prefixLift 192729
  have htrace : WordTrace (prefixWord ++ tailWord_192729) baseStart_192729 baseEnd_192729 := by
    simpa [prefixWord, tailWord_192729, baseEnd_192729] using wordTrace_append hprefix tailTrace_192729
  have hstable : (prefixWord ++ tailWord_192729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192729).length < 2 ^ (prefixWord ++ tailWord_192729).sum := by decide
  have hdescent : baseEnd_192729 < baseStart_192729 := by decide
  rcases family_descends (prefixWord ++ tailWord_192729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192791 : List Nat := [1, 1, 3, 4, 1, 4, 1, 6]
def baseStart_192791 : Nat := 118140960795 + 192791 * 2 ^ 59
def prefixEnd_192791 : Nat := 4983230072969 + 3 ^ 40 * 192791 * 2
def baseEnd_192791 : Nat := 14665844275712657485315

theorem tailTrace_192791 : CollatzResearch.WordTrace tailWord_192791 prefixEnd_192791 14665844275712657485315 := by
  unfold tailWord_192791
  simp only [CollatzResearch.WordTrace]
  refine ⟨7031665444558607926530227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4687776963039071951020151 7031665444558607926530227)
  ·
    refine ⟨10547498166837911889795341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7031665444558607926530227 10547498166837911889795341)
    ·
      refine ⟨3955311812564216958673253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10547498166837911889795341 3955311812564216958673253)
      ·
        refine ⟨741620964855790679751235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3955311812564216958673253 741620964855790679751235)
        ·
          refine ⟨1112431447283686019626853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 741620964855790679751235 1112431447283686019626853)
          ·
            refine ⟨208580896365691128680035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1112431447283686019626853 208580896365691128680035)
            ·
              refine ⟨312871344548536693020053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208580896365691128680035 312871344548536693020053)
              ·
                refine ⟨14665844275712657485315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 312871344548536693020053 14665844275712657485315)
                ·
                  rfl

theorem cell21_192791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 6].length) (baseStart_192791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_192791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_192791 prefixEnd_192791 := by exact prefixLift 192791
  have htrace : WordTrace (prefixWord ++ tailWord_192791) baseStart_192791 baseEnd_192791 := by
    simpa [prefixWord, tailWord_192791, baseEnd_192791] using wordTrace_append hprefix tailTrace_192791
  have hstable : (prefixWord ++ tailWord_192791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192791).length < 2 ^ (prefixWord ++ tailWord_192791).sum := by decide
  have hdescent : baseEnd_192791 < baseStart_192791 := by decide
  rcases family_descends (prefixWord ++ tailWord_192791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192808 : List Nat := [2, 1, 5, 1, 3, 1, 3, 5]
def baseStart_192808 : Nat := 118140960795 + 192808 * 2 ^ 59
def prefixEnd_192808 : Nat := 4983230072969 + 3 ^ 40 * 192808 * 2
def baseEnd_192808 : Nat := 14667137486249906890859

theorem tailTrace_192808 : CollatzResearch.WordTrace tailWord_192808 prefixEnd_192808 14667137486249906890859 := by
  unfold tailWord_192808
  simp only [CollatzResearch.WordTrace]
  refine ⟨3516142742748509914949539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4688190323664679886599385 3516142742748509914949539)
  ·
    refine ⟨5274214114122764872424309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3516142742748509914949539 5274214114122764872424309)
    ·
      refine ⟨494457573199009206789779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5274214114122764872424309 494457573199009206789779)
      ·
        refine ⟨741686359798513810184669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494457573199009206789779 741686359798513810184669)
        ·
          refine ⟨278132384924442678819251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 741686359798513810184669 278132384924442678819251)
          ·
            refine ⟨417198577386664018228877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278132384924442678819251 417198577386664018228877)
            ·
              refine ⟨156449466519999006835829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 417198577386664018228877 156449466519999006835829)
              ·
                refine ⟨14667137486249906890859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156449466519999006835829 14667137486249906890859)
                ·
                  rfl

theorem cell21_192808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 5].length) (baseStart_192808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_192808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_192808 prefixEnd_192808 := by exact prefixLift 192808
  have htrace : WordTrace (prefixWord ++ tailWord_192808) baseStart_192808 baseEnd_192808 := by
    simpa [prefixWord, tailWord_192808, baseEnd_192808] using wordTrace_append hprefix tailTrace_192808
  have hstable : (prefixWord ++ tailWord_192808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192808).length < 2 ^ (prefixWord ++ tailWord_192808).sum := by decide
  have hdescent : baseEnd_192808 < baseStart_192808 := by decide
  rcases family_descends (prefixWord ++ tailWord_192808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192819 : List Nat := [1, 1, 1, 2, 5, 1, 2, 2, 6]
def baseStart_192819 : Nat := 118140960795 + 192819 * 2 ^ 59
def prefixEnd_192819 : Nat := 4983230072969 + 3 ^ 40 * 192819 * 2
def baseEnd_192819 : Nat := 44003922808616145989221

theorem tailTrace_192819 : CollatzResearch.WordTrace tailWord_192819 prefixEnd_192819 44003922808616145989221 := by
  unfold tailWord_192819
  simp only [CollatzResearch.WordTrace]
  refine ⟨7032686688457168708549511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4688457792304779139033007 7032686688457168708549511)
  ·
    refine ⟨10549030032685753062824267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7032686688457168708549511 10549030032685753062824267)
    ·
      refine ⟨15823545049028629594236401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10549030032685753062824267 15823545049028629594236401)
      ·
        refine ⟨11867658786771472195677301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15823545049028629594236401 11867658786771472195677301)
        ·
          refine ⟨1112593011259825518344747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11867658786771472195677301 1112593011259825518344747)
          ·
            refine ⟨1668889516889738277517121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1112593011259825518344747 1668889516889738277517121)
            ·
              refine ⟨1251667137667303708137841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1668889516889738277517121 1251667137667303708137841)
              ·
                refine ⟨938750353250477781103381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1251667137667303708137841 938750353250477781103381)
                ·
                  refine ⟨44003922808616145989221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 938750353250477781103381 44003922808616145989221)
                  ·
                    rfl

theorem cell21_192819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 6].length) (baseStart_192819 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_192819 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_192819 prefixEnd_192819 := by exact prefixLift 192819
  have htrace : WordTrace (prefixWord ++ tailWord_192819) baseStart_192819 baseEnd_192819 := by
    simpa [prefixWord, tailWord_192819, baseEnd_192819] using wordTrace_append hprefix tailTrace_192819
  have hstable : (prefixWord ++ tailWord_192819).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192819).length < 2 ^ (prefixWord ++ tailWord_192819).sum := by decide
  have hdescent : baseEnd_192819 < baseStart_192819 := by decide
  rcases family_descends (prefixWord ++ tailWord_192819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192949 : List Nat := [1, 3, 3, 2, 4, 1, 2, 2, 3]
def baseStart_192949 : Nat := 118140960795 + 192949 * 2 ^ 59
def prefixEnd_192949 : Nat := 4983230072969 + 3 ^ 40 * 192949 * 2
def baseEnd_192949 : Nat := 44033590579764808822289

theorem tailTrace_192949 : CollatzResearch.WordTrace tailWord_192949 prefixEnd_192949 44033590579764808822289 := by
  unfold tailWord_192949
  simp only [CollatzResearch.WordTrace]
  refine ⟨7037428177986200910781901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4691618785324133940521267 7037428177986200910781901)
  ·
    refine ⟨2639035566744825341543213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7037428177986200910781901 2639035566744825341543213)
    ·
      refine ⟨989638337529309503078705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2639035566744825341543213 989638337529309503078705)
      ·
        refine ⟨742228753146982127309029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 989638337529309503078705 742228753146982127309029)
        ·
          refine ⟨139167891215059148870443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 742228753146982127309029 139167891215059148870443)
          ·
            refine ⟨208751836822588723305665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139167891215059148870443 208751836822588723305665)
            ·
              refine ⟨156563877616941542479249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208751836822588723305665 156563877616941542479249)
              ·
                refine ⟨117422908212706156859437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156563877616941542479249 117422908212706156859437)
                ·
                  refine ⟨44033590579764808822289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117422908212706156859437 44033590579764808822289)
                  ·
                    rfl

theorem cell21_192949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2, 3].length) (baseStart_192949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_192949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_192949 prefixEnd_192949 := by exact prefixLift 192949
  have htrace : WordTrace (prefixWord ++ tailWord_192949) baseStart_192949 baseEnd_192949 := by
    simpa [prefixWord, tailWord_192949, baseEnd_192949] using wordTrace_append hprefix tailTrace_192949
  have hstable : (prefixWord ++ tailWord_192949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192949).length < 2 ^ (prefixWord ++ tailWord_192949).sum := by decide
  have hdescent : baseEnd_192949 < baseStart_192949 := by decide
  rcases family_descends (prefixWord ++ tailWord_192949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193002 : List Nat := [3, 1, 3, 1, 3, 2, 8]
def baseStart_193002 : Nat := 118140960795 + 193002 * 2 ^ 59
def prefixEnd_193002 : Nat := 4983230072969 + 3 ^ 40 * 193002 * 2
def baseEnd_193002 : Nat := 4893965100205388270983

theorem tailTrace_193002 : CollatzResearch.WordTrace tailWord_193002 prefixEnd_193002 4893965100205388270983 := by
  unfold tailWord_193002
  simp only [CollatzResearch.WordTrace]
  refine ⟨1759840311698547740615315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4692907497862793974974173 1759840311698547740615315)
  ·
    refine ⟨2639760467547821610922973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1759840311698547740615315 2639760467547821610922973)
    ·
      refine ⟨989910175330433104096115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2639760467547821610922973 989910175330433104096115)
      ·
        refine ⟨1484865262995649656144173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 989910175330433104096115 1484865262995649656144173)
        ·
          refine ⟨556824473623368621054065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1484865262995649656144173 556824473623368621054065)
          ·
            refine ⟨417618355217526465790549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 556824473623368621054065 417618355217526465790549)
            ·
              refine ⟨4893965100205388270983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 417618355217526465790549 4893965100205388270983)
              ·
                rfl

theorem cell21_193002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 8].length) (baseStart_193002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_193002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_193002 prefixEnd_193002 := by exact prefixLift 193002
  have htrace : WordTrace (prefixWord ++ tailWord_193002) baseStart_193002 baseEnd_193002 := by
    simpa [prefixWord, tailWord_193002, baseEnd_193002] using wordTrace_append hprefix tailTrace_193002
  have hstable : (prefixWord ++ tailWord_193002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193002).length < 2 ^ (prefixWord ++ tailWord_193002).sum := by decide
  have hdescent : baseEnd_193002 < baseStart_193002 := by decide
  rcases family_descends (prefixWord ++ tailWord_193002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193005 : List Nat := [1, 5, 1, 3, 1, 1, 3, 2, 4]
def baseStart_193005 : Nat := 118140960795 + 193005 * 2 ^ 59
def prefixEnd_193005 : Nat := 4983230072969 + 3 ^ 40 * 193005 * 2
def baseEnd_193005 : Nat := 44046370542721155888841

theorem tailTrace_193005 : CollatzResearch.WordTrace tailWord_193005 prefixEnd_193005 44046370542721155888841 := by
  unfold tailWord_193005
  simp only [CollatzResearch.WordTrace]
  refine ⟨7039470665783322474820469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4692980443855548316546979 7039470665783322474820469)
  ·
    refine ⟨659950374917186482014419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7039470665783322474820469 659950374917186482014419)
    ·
      refine ⟨989925562375779723021629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 659950374917186482014419 989925562375779723021629)
      ·
        refine ⟨371222085890917396133111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 989925562375779723021629 371222085890917396133111)
        ·
          refine ⟨556833128836376094199667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371222085890917396133111 556833128836376094199667)
          ·
            refine ⟨835249693254564141299501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556833128836376094199667 835249693254564141299501)
            ·
              refine ⟨313218634970461552987313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 835249693254564141299501 313218634970461552987313)
              ·
                refine ⟨234913976227846164740485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313218634970461552987313 234913976227846164740485)
                ·
                  refine ⟨44046370542721155888841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 234913976227846164740485 44046370542721155888841)
                  ·
                    rfl

theorem cell21_193005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_193005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_193005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_193005 prefixEnd_193005 := by exact prefixLift 193005
  have htrace : WordTrace (prefixWord ++ tailWord_193005) baseStart_193005 baseEnd_193005 := by
    simpa [prefixWord, tailWord_193005, baseEnd_193005] using wordTrace_append hprefix tailTrace_193005
  have hstable : (prefixWord ++ tailWord_193005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193005).length < 2 ^ (prefixWord ++ tailWord_193005).sum := by decide
  have hdescent : baseEnd_193005 < baseStart_193005 := by decide
  rcases family_descends (prefixWord ++ tailWord_193005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193050 : List Nat := [3, 1, 1, 3, 1, 1, 5, 3, 3]
def baseStart_193050 : Nat := 118140960795 + 193050 * 2 ^ 59
def prefixEnd_193050 : Nat := 4983230072969 + 3 ^ 40 * 193050 * 2
def baseEnd_193050 : Nat := 44056640155811077638749

theorem tailTrace_193050 : CollatzResearch.WordTrace tailWord_193050 prefixEnd_193050 44056640155811077638749 := by
  unfold tailWord_193050
  simp only [CollatzResearch.WordTrace]
  refine ⟨1760277987655073790052151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4694074633746863440139069 1760277987655073790052151)
  ·
    refine ⟨2640416981482610685078227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1760277987655073790052151 2640416981482610685078227)
    ·
      refine ⟨3960625472223916027617341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2640416981482610685078227 3960625472223916027617341)
      ·
        refine ⟨1485234552083968510356503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3960625472223916027617341 1485234552083968510356503)
        ·
          refine ⟨2227851828125952765534755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1485234552083968510356503 2227851828125952765534755)
          ·
            refine ⟨3341777742188929148302133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2227851828125952765534755 3341777742188929148302133)
            ·
              refine ⟨313291663330212107653325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3341777742188929148302133 313291663330212107653325)
              ·
                refine ⟨117484373748829540369997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 313291663330212107653325 117484373748829540369997)
                ·
                  refine ⟨44056640155811077638749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117484373748829540369997 44056640155811077638749)
                  ·
                    rfl

theorem cell21_193050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3, 3].length) (baseStart_193050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_193050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_193050 prefixEnd_193050 := by exact prefixLift 193050
  have htrace : WordTrace (prefixWord ++ tailWord_193050) baseStart_193050 baseEnd_193050 := by
    simpa [prefixWord, tailWord_193050, baseEnd_193050] using wordTrace_append hprefix tailTrace_193050
  have hstable : (prefixWord ++ tailWord_193050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193050).length < 2 ^ (prefixWord ++ tailWord_193050).sum := by decide
  have hdescent : baseEnd_193050 < baseStart_193050 := by decide
  rcases family_descends (prefixWord ++ tailWord_193050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193061 : List Nat := [1, 3, 1, 2, 2, 1, 11]
def baseStart_193061 : Nat := 118140960795 + 193061 * 2 ^ 59
def prefixEnd_193061 : Nat := 4983230072969 + 3 ^ 40 * 193061 * 2
def baseEnd_193061 : Nat := 4895461167297500328377

theorem tailTrace_193061 : CollatzResearch.WordTrace tailWord_193061 prefixEnd_193061 4895461167297500328377 := by
  unfold tailWord_193061
  simp only [CollatzResearch.WordTrace]
  refine ⟨7041513153580444038859037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4694342102386962692572691 7041513153580444038859037)
  ·
    refine ⟨2640567432592666514572139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7041513153580444038859037 2640567432592666514572139)
    ·
      refine ⟨3960851148888999771858209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2640567432592666514572139 3960851148888999771858209)
      ·
        refine ⟨2970638361666749828893657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3960851148888999771858209 2970638361666749828893657)
        ·
          refine ⟨2227978771250062371670243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2970638361666749828893657 2227978771250062371670243)
          ·
            refine ⟨3341968156875093557505365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2227978771250062371670243 3341968156875093557505365)
            ·
              refine ⟨4895461167297500328377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 3341968156875093557505365 4895461167297500328377)
              ·
                rfl

theorem cell21_193061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 11].length) (baseStart_193061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_193061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_193061 prefixEnd_193061 := by exact prefixLift 193061
  have htrace : WordTrace (prefixWord ++ tailWord_193061) baseStart_193061 baseEnd_193061 := by
    simpa [prefixWord, tailWord_193061, baseEnd_193061] using wordTrace_append hprefix tailTrace_193061
  have hstable : (prefixWord ++ tailWord_193061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193061).length < 2 ^ (prefixWord ++ tailWord_193061).sum := by decide
  have hdescent : baseEnd_193061 < baseStart_193061 := by decide
  rcases family_descends (prefixWord ++ tailWord_193061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193064 : List Nat := [2, 1, 5, 2, 1, 1, 2, 1, 6]
def baseStart_193064 : Nat := 118140960795 + 193064 * 2 ^ 59
def prefixEnd_193064 : Nat := 4983230072969 + 3 ^ 40 * 193064 * 2
def baseEnd_193064 : Nat := 44059835146550164405387

theorem tailTrace_193064 : CollatzResearch.WordTrace tailWord_193064 prefixEnd_193064 44059835146550164405387 := by
  unfold tailWord_193064
  simp only [CollatzResearch.WordTrace]
  refine ⟨3520811286284787775609123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4694415048379717034145497 3520811286284787775609123)
  ·
    refine ⟨5281216929427181663413685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3520811286284787775609123 5281216929427181663413685)
    ·
      refine ⟨495114087133798280945033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5281216929427181663413685 495114087133798280945033)
      ·
        refine ⟨371335565350348710708775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 495114087133798280945033 371335565350348710708775)
        ·
          refine ⟨557003348025523066063163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371335565350348710708775 557003348025523066063163)
          ·
            refine ⟨835505022038284599094745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557003348025523066063163 835505022038284599094745)
            ·
              refine ⟨626628766528713449321059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 835505022038284599094745 626628766528713449321059)
              ·
                refine ⟨939943149793070173981589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626628766528713449321059 939943149793070173981589)
                ·
                  refine ⟨44059835146550164405387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 939943149793070173981589 44059835146550164405387)
                  ·
                    rfl

theorem cell21_193064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 6].length) (baseStart_193064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_193064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_193064 prefixEnd_193064 := by exact prefixLift 193064
  have htrace : WordTrace (prefixWord ++ tailWord_193064) baseStart_193064 baseEnd_193064 := by
    simpa [prefixWord, tailWord_193064, baseEnd_193064] using wordTrace_append hprefix tailTrace_193064
  have hstable : (prefixWord ++ tailWord_193064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193064).length < 2 ^ (prefixWord ++ tailWord_193064).sum := by decide
  have hdescent : baseEnd_193064 < baseStart_193064 := by decide
  rcases family_descends (prefixWord ++ tailWord_193064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193230 : List Nat := [4, 1, 1, 1, 3, 4, 7]
def baseStart_193230 : Nat := 118140960795 + 193230 * 2 ^ 59
def prefixEnd_193230 : Nat := 4983230072969 + 3 ^ 40 * 193230 * 2
def baseEnd_193230 : Nat := 4899746512018973848709

theorem tailTrace_193230 : CollatzResearch.WordTrace tailWord_193230 prefixEnd_193230 4899746512018973848709 := by
  unfold tailWord_193230
  simp only [CollatzResearch.WordTrace]
  refine ⟨880959636246023237720143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4698451393312123934507429 880959636246023237720143)
  ·
    refine ⟨1321439454369034856580215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 880959636246023237720143 1321439454369034856580215)
    ·
      refine ⟨1982159181553552284870323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1321439454369034856580215 1982159181553552284870323)
      ·
        refine ⟨2973238772330328427305485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1982159181553552284870323 2973238772330328427305485)
        ·
          refine ⟨1114964539623873160239557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2973238772330328427305485 1114964539623873160239557)
          ·
            refine ⟨209055851179476217544917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1114964539623873160239557 209055851179476217544917)
            ·
              refine ⟨4899746512018973848709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 209055851179476217544917 4899746512018973848709)
              ·
                rfl

theorem cell21_193230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 7].length) (baseStart_193230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_193230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_193230 prefixEnd_193230 := by exact prefixLift 193230
  have htrace : WordTrace (prefixWord ++ tailWord_193230) baseStart_193230 baseEnd_193230 := by
    simpa [prefixWord, tailWord_193230, baseEnd_193230] using wordTrace_append hprefix tailTrace_193230
  have hstable : (prefixWord ++ tailWord_193230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193230).length < 2 ^ (prefixWord ++ tailWord_193230).sum := by decide
  have hdescent : baseEnd_193230 < baseStart_193230 := by decide
  rcases family_descends (prefixWord ++ tailWord_193230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193236 : List Nat := [2, 4, 1, 3, 2, 1, 3, 2, 3]
def baseStart_193236 : Nat := 118140960795 + 193236 * 2 ^ 59
def prefixEnd_193236 : Nat := 4983230072969 + 3 ^ 40 * 193236 * 2
def baseEnd_193236 : Nat := 44099087889916087538369

theorem tailTrace_193236 : CollatzResearch.WordTrace tailWord_193236 prefixEnd_193236 44099087889916087538369 := by
  unfold tailWord_193236
  simp only [CollatzResearch.WordTrace]
  refine ⟨3523947963973224463239781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4698597285297632617653041 3523947963973224463239781)
  ·
    refine ⟨660740243244979586857459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3523947963973224463239781 660740243244979586857459)
    ·
      refine ⟨991110364867469380286189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 660740243244979586857459 991110364867469380286189)
      ·
        refine ⟨371666386825301017607321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 991110364867469380286189 371666386825301017607321)
        ·
          refine ⟨278749790118975763205491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371666386825301017607321 278749790118975763205491)
          ·
            refine ⟨418124685178463644808237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278749790118975763205491 418124685178463644808237)
            ·
              refine ⟨156796756941923866803089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 418124685178463644808237 156796756941923866803089)
              ·
                refine ⟨117597567706442900102317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156796756941923866803089 117597567706442900102317)
                ·
                  refine ⟨44099087889916087538369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117597567706442900102317 44099087889916087538369)
                  ·
                    rfl

theorem cell21_193236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_193236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_193236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_193236 prefixEnd_193236 := by exact prefixLift 193236
  have htrace : WordTrace (prefixWord ++ tailWord_193236) baseStart_193236 baseEnd_193236 := by
    simpa [prefixWord, tailWord_193236, baseEnd_193236] using wordTrace_append hprefix tailTrace_193236
  have hstable : (prefixWord ++ tailWord_193236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193236).length < 2 ^ (prefixWord ++ tailWord_193236).sum := by decide
  have hdescent : baseEnd_193236 < baseStart_193236 := by decide
  rcases family_descends (prefixWord ++ tailWord_193236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193365 : List Nat := [1, 3, 2, 2, 2, 1, 2, 8]
def baseStart_193365 : Nat := 118140960795 + 193365 * 2 ^ 59
def prefixEnd_193365 : Nat := 4983230072969 + 3 ^ 40 * 193365 * 2
def baseEnd_193365 : Nat := 14709509149146843296035

theorem tailTrace_193365 : CollatzResearch.WordTrace tailWord_193365 prefixEnd_193365 14709509149146843296035 := by
  unfold tailWord_193365
  simp only [CollatzResearch.WordTrace]
  refine ⟨7052600944479103957925549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4701733962986069305283699 7052600944479103957925549)
  ·
    refine ⟨2644725354179663984222081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7052600944479103957925549 2644725354179663984222081)
    ·
      refine ⟨1983544015634747988166561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2644725354179663984222081 1983544015634747988166561)
      ·
        refine ⟨1487658011726060991124921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1983544015634747988166561 1487658011726060991124921)
        ·
          refine ⟨1115743508794545743343691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1487658011726060991124921 1115743508794545743343691)
          ·
            refine ⟨1673615263191818615015537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1115743508794545743343691 1673615263191818615015537)
            ·
              refine ⟨1255211447393863961261653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1673615263191818615015537 1255211447393863961261653)
              ·
                refine ⟨14709509149146843296035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1255211447393863961261653 14709509149146843296035)
                ·
                  rfl

theorem cell21_193365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 8].length) (baseStart_193365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_193365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_193365 prefixEnd_193365 := by exact prefixLift 193365
  have htrace : WordTrace (prefixWord ++ tailWord_193365) baseStart_193365 baseEnd_193365 := by
    simpa [prefixWord, tailWord_193365, baseEnd_193365] using wordTrace_append hprefix tailTrace_193365
  have hstable : (prefixWord ++ tailWord_193365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193365).length < 2 ^ (prefixWord ++ tailWord_193365).sum := by decide
  have hdescent : baseEnd_193365 < baseStart_193365 := by decide
  rcases family_descends (prefixWord ++ tailWord_193365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193413 : List Nat := [1, 3, 1, 1, 3, 5, 1, 1, 5]
def baseStart_193413 : Nat := 118140960795 + 193413 * 2 ^ 59
def prefixEnd_193413 : Nat := 4983230072969 + 3 ^ 40 * 193413 * 2
def baseEnd_193413 : Nat := 44139481701403113088007

theorem tailTrace_193413 : CollatzResearch.WordTrace tailWord_193413 prefixEnd_193413 44139481701403113088007 := by
  unfold tailWord_193413
  simp only [CollatzResearch.WordTrace]
  refine ⟨7054351648305208155672893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4702901098870138770448595 7054351648305208155672893)
  ·
    refine ⟨2645381868114453058377335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7054351648305208155672893 2645381868114453058377335)
    ·
      refine ⟨3968072802171679587566003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2645381868114453058377335 3968072802171679587566003)
      ·
        refine ⟨5952109203257519381349005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3968072802171679587566003 5952109203257519381349005)
        ·
          refine ⟨2232040951221569768005877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5952109203257519381349005 2232040951221569768005877)
          ·
            refine ⟨209253839177022165750551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2232040951221569768005877 209253839177022165750551)
            ·
              refine ⟨313880758765533248625827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209253839177022165750551 313880758765533248625827)
              ·
                refine ⟨470821138148299872938741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313880758765533248625827 470821138148299872938741)
                ·
                  refine ⟨44139481701403113088007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 470821138148299872938741 44139481701403113088007)
                  ·
                    rfl

theorem cell21_193413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_193413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_193413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_193413 prefixEnd_193413 := by exact prefixLift 193413
  have htrace : WordTrace (prefixWord ++ tailWord_193413) baseStart_193413 baseEnd_193413 := by
    simpa [prefixWord, tailWord_193413, baseEnd_193413] using wordTrace_append hprefix tailTrace_193413
  have hstable : (prefixWord ++ tailWord_193413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193413).length < 2 ^ (prefixWord ++ tailWord_193413).sum := by decide
  have hdescent : baseEnd_193413 < baseStart_193413 := by decide
  rcases family_descends (prefixWord ++ tailWord_193413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193455 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 9]
def baseStart_193455 : Nat := 118140960795 + 193455 * 2 ^ 59
def prefixEnd_193455 : Nat := 4983230072969 + 3 ^ 40 * 193455 * 2
def baseEnd_193455 : Nat := 44149066673620373387921

theorem tailTrace_193455 : CollatzResearch.WordTrace tailWord_193455 prefixEnd_193455 44149066673620373387921 := by
  unfold tailWord_193455
  simp only [CollatzResearch.WordTrace]
  refine ⟨7055883514153049328701819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4703922342768699552467879 7055883514153049328701819)
  ·
    refine ⟨10583825271229573993052729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7055883514153049328701819 10583825271229573993052729)
    ·
      refine ⟨7937868953422180494789547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10583825271229573993052729 7937868953422180494789547)
      ·
        refine ⟨11906803430133270742184321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7937868953422180494789547 11906803430133270742184321)
        ·
          refine ⟨8930102572599953056638241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11906803430133270742184321 8930102572599953056638241)
          ·
            refine ⟨6697576929449964792478681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8930102572599953056638241 6697576929449964792478681)
            ·
              refine ⟨5023182697087473594359011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6697576929449964792478681 5023182697087473594359011)
              ·
                refine ⟨7534774045631210391538517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5023182697087473594359011 7534774045631210391538517)
                ·
                  refine ⟨44149066673620373387921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7534774045631210391538517 44149066673620373387921)
                  ·
                    rfl

theorem cell21_193455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 9].length) (baseStart_193455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_193455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_193455 prefixEnd_193455 := by exact prefixLift 193455
  have htrace : WordTrace (prefixWord ++ tailWord_193455) baseStart_193455 baseEnd_193455 := by
    simpa [prefixWord, tailWord_193455, baseEnd_193455] using wordTrace_append hprefix tailTrace_193455
  have hstable : (prefixWord ++ tailWord_193455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193455).length < 2 ^ (prefixWord ++ tailWord_193455).sum := by decide
  have hdescent : baseEnd_193455 < baseStart_193455 := by decide
  rcases family_descends (prefixWord ++ tailWord_193455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193548 : List Nat := [2, 2, 1, 2, 3, 2, 2, 2, 5]
def baseStart_193548 : Nat := 118140960795 + 193548 * 2 ^ 59
def prefixEnd_193548 : Nat := 4983230072969 + 3 ^ 40 * 193548 * 2
def baseEnd_193548 : Nat := 44170290540672878337731

theorem tailTrace_193548 : CollatzResearch.WordTrace tailWord_193548 prefixEnd_193548 44170290540672878337731 := by
  unfold tailWord_193548
  simp only [CollatzResearch.WordTrace]
  refine ⟨3529637751408063105918649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4706183668544084141224865 3529637751408063105918649)
  ·
    refine ⟨2647228313556047329438987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3529637751408063105918649 2647228313556047329438987)
    ·
      refine ⟨3970842470334070994158481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2647228313556047329438987 3970842470334070994158481)
      ·
        refine ⟨2978131852750553245618861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3970842470334070994158481 2978131852750553245618861)
        ·
          refine ⟨1116799444781457467107073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2978131852750553245618861 1116799444781457467107073)
          ·
            refine ⟨837599583586093100330305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1116799444781457467107073 837599583586093100330305)
            ·
              refine ⟨628199687689569825247729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 837599583586093100330305 628199687689569825247729)
              ·
                refine ⟨471149765767177368935797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 628199687689569825247729 471149765767177368935797)
                ·
                  refine ⟨44170290540672878337731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 471149765767177368935797 44170290540672878337731)
                  ·
                    rfl

theorem cell21_193548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_193548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_193548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_193548 prefixEnd_193548 := by exact prefixLift 193548
  have htrace : WordTrace (prefixWord ++ tailWord_193548) baseStart_193548 baseEnd_193548 := by
    simpa [prefixWord, tailWord_193548, baseEnd_193548] using wordTrace_append hprefix tailTrace_193548
  have hstable : (prefixWord ++ tailWord_193548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193548).length < 2 ^ (prefixWord ++ tailWord_193548).sum := by decide
  have hdescent : baseEnd_193548 < baseStart_193548 := by decide
  rcases family_descends (prefixWord ++ tailWord_193548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193562 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 8]
def baseStart_193562 : Nat := 118140960795 + 193562 * 2 ^ 59
def prefixEnd_193562 : Nat := 4983230072969 + 3 ^ 40 * 193562 * 2
def baseEnd_193562 : Nat := 44173485531411965104369

theorem tailTrace_193562 : CollatzResearch.WordTrace tailWord_193562 prefixEnd_193562 44173485531411965104369 := by
  unfold tailWord_193562
  simp only [CollatzResearch.WordTrace]
  refine ⟨1764946531191351650711735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4706524083176937735231293 1764946531191351650711735)
  ·
    refine ⟨2647419796787027476067603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1764946531191351650711735 2647419796787027476067603)
    ·
      refine ⟨3971129695180541214101405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2647419796787027476067603 3971129695180541214101405)
      ·
        refine ⟨1489173635692702955288027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3971129695180541214101405 1489173635692702955288027)
        ·
          refine ⟨2233760453539054432932041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1489173635692702955288027 2233760453539054432932041)
          ·
            refine ⟨1675320340154290824699031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2233760453539054432932041 1675320340154290824699031)
            ·
              refine ⟨2512980510231436237048547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1675320340154290824699031 2512980510231436237048547)
              ·
                refine ⟨3769470765347154355572821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2512980510231436237048547 3769470765347154355572821)
                ·
                  refine ⟨44173485531411965104369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3769470765347154355572821 44173485531411965104369)
                  ·
                    rfl

theorem cell21_193562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_193562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_193562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_193562 prefixEnd_193562 := by exact prefixLift 193562
  have htrace : WordTrace (prefixWord ++ tailWord_193562) baseStart_193562 baseEnd_193562 := by
    simpa [prefixWord, tailWord_193562, baseEnd_193562] using wordTrace_append hprefix tailTrace_193562
  have hstable : (prefixWord ++ tailWord_193562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193562).length < 2 ^ (prefixWord ++ tailWord_193562).sum := by decide
  have hdescent : baseEnd_193562 < baseStart_193562 := by decide
  rcases family_descends (prefixWord ++ tailWord_193562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193593 : List Nat := [1, 2, 1, 5, 2, 1, 1, 8]
def baseStart_193593 : Nat := 118140960795 + 193593 * 2 ^ 59
def prefixEnd_193593 : Nat := 4983230072969 + 3 ^ 40 * 193593 * 2
def baseEnd_193593 : Nat := 14726853384587600029213

theorem tailTrace_193593 : CollatzResearch.WordTrace tailWord_193593 prefixEnd_193593 14726853384587600029213 := by
  unfold tailWord_193593
  simp only [CollatzResearch.WordTrace]
  refine ⟨7060916787653098897225433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4707277858435399264816955 7060916787653098897225433)
  ·
    refine ⟨5295687590739824172919075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7060916787653098897225433 5295687590739824172919075)
    ·
      refine ⟨7943531386109736259378613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5295687590739824172919075 7943531386109736259378613)
      ·
        refine ⟨744706067447787774316745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7943531386109736259378613 744706067447787774316745)
        ·
          refine ⟨558529550585840830737559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 744706067447787774316745 558529550585840830737559)
          ·
            refine ⟨837794325878761246106339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558529550585840830737559 837794325878761246106339)
            ·
              refine ⟨1256691488818141869159509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 837794325878761246106339 1256691488818141869159509)
              ·
                refine ⟨14726853384587600029213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1256691488818141869159509 14726853384587600029213)
                ·
                  rfl

theorem cell21_193593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 8].length) (baseStart_193593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_193593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_193593 prefixEnd_193593 := by exact prefixLift 193593
  have htrace : WordTrace (prefixWord ++ tailWord_193593) baseStart_193593 baseEnd_193593 := by
    simpa [prefixWord, tailWord_193593, baseEnd_193593] using wordTrace_append hprefix tailTrace_193593
  have hstable : (prefixWord ++ tailWord_193593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193593).length < 2 ^ (prefixWord ++ tailWord_193593).sum := by decide
  have hdescent : baseEnd_193593 < baseStart_193593 := by decide
  rcases family_descends (prefixWord ++ tailWord_193593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193596 : List Nat := [2, 2, 2, 2, 2, 2, 4, 1, 4]
def baseStart_193596 : Nat := 118140960795 + 193596 * 2 ^ 59
def prefixEnd_193596 : Nat := 4983230072969 + 3 ^ 40 * 193596 * 2
def baseEnd_193596 : Nat := 44181244794635461537633

theorem tailTrace_193596 : CollatzResearch.WordTrace tailWord_193596 prefixEnd_193596 44181244794635461537633 := by
  unfold tailWord_193596
  simp only [CollatzResearch.WordTrace]
  refine ⟨3530513103321115204792321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4707350804428153606389761 3530513103321115204792321)
  ·
    refine ⟨2647884827490836403594241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3530513103321115204792321 2647884827490836403594241)
    ·
      refine ⟨1985913620618127302695681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2647884827490836403594241 1985913620618127302695681)
      ·
        refine ⟨1489435215463595477021761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1985913620618127302695681 1489435215463595477021761)
        ·
          refine ⟨1117076411597696607766321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1489435215463595477021761 1117076411597696607766321)
          ·
            refine ⟨837807308698272455824741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1117076411597696607766321 837807308698272455824741)
            ·
              refine ⟨157088870380926085467139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 837807308698272455824741 157088870380926085467139)
              ·
                refine ⟨235633305571389128200709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157088870380926085467139 235633305571389128200709)
                ·
                  refine ⟨44181244794635461537633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 235633305571389128200709 44181244794635461537633)
                  ·
                    rfl

theorem cell21_193596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_193596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_193596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_193596 prefixEnd_193596 := by exact prefixLift 193596
  have htrace : WordTrace (prefixWord ++ tailWord_193596) baseStart_193596 baseEnd_193596 := by
    simpa [prefixWord, tailWord_193596, baseEnd_193596] using wordTrace_append hprefix tailTrace_193596
  have hstable : (prefixWord ++ tailWord_193596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193596).length < 2 ^ (prefixWord ++ tailWord_193596).sum := by decide
  have hdescent : baseEnd_193596 < baseStart_193596 := by decide
  rcases family_descends (prefixWord ++ tailWord_193596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193630 : List Nat := [4, 4, 1, 1, 1, 2, 2, 2, 4]
def baseStart_193630 : Nat := 118140960795 + 193630 * 2 ^ 59
def prefixEnd_193630 : Nat := 4983230072969 + 3 ^ 40 * 193630 * 2
def baseEnd_193630 : Nat := 44189004057858957970897

theorem tailTrace_193630 : CollatzResearch.WordTrace tailWord_193630 prefixEnd_193630 44189004057858957970897 := by
  unfold tailWord_193630
  simp only [CollatzResearch.WordTrace]
  refine ⟨882783286064881777040293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4708177525679369477548229 882783286064881777040293)
  ·
    refine ⟨165521866137165333195055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 882783286064881777040293 165521866137165333195055)
    ·
      refine ⟨248282799205747999792583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165521866137165333195055 248282799205747999792583)
      ·
        refine ⟨372424198808621999688875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248282799205747999792583 372424198808621999688875)
        ·
          refine ⟨558636298212932999533313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372424198808621999688875 558636298212932999533313)
          ·
            refine ⟨418977223659699749649985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 558636298212932999533313 418977223659699749649985)
            ·
              refine ⟨314232917744774812237489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418977223659699749649985 314232917744774812237489)
              ·
                refine ⟨235674688308581109178117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314232917744774812237489 235674688308581109178117)
                ·
                  refine ⟨44189004057858957970897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 235674688308581109178117 44189004057858957970897)
                  ·
                    rfl

theorem cell21_193630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_193630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_193630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_193630 prefixEnd_193630 := by exact prefixLift 193630
  have htrace : WordTrace (prefixWord ++ tailWord_193630) baseStart_193630 baseEnd_193630 := by
    simpa [prefixWord, tailWord_193630, baseEnd_193630] using wordTrace_append hprefix tailTrace_193630
  have hstable : (prefixWord ++ tailWord_193630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193630).length < 2 ^ (prefixWord ++ tailWord_193630).sum := by decide
  have hdescent : baseEnd_193630 < baseStart_193630 := by decide
  rcases family_descends (prefixWord ++ tailWord_193630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193641 : List Nat := [1, 2, 1, 1, 1, 7, 1, 4, 3]
def baseStart_193641 : Nat := 118140960795 + 193641 * 2 ^ 59
def prefixEnd_193641 : Nat := 4983230072969 + 3 ^ 40 * 193641 * 2
def baseEnd_193641 : Nat := 44191514407725383287541

theorem tailTrace_193641 : CollatzResearch.WordTrace tailWord_193641 prefixEnd_193641 44191514407725383287541 := by
  unfold tailWord_193641
  simp only [CollatzResearch.WordTrace]
  refine ⟨7062667491479203094972777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4708444994319468729981851 7062667491479203094972777)
  ·
    refine ⟨5297000618609402321229583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7062667491479203094972777 5297000618609402321229583)
    ·
      refine ⟨7945500927914103481844375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5297000618609402321229583 7945500927914103481844375)
      ·
        refine ⟨11918251391871155222766563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7945500927914103481844375 11918251391871155222766563)
        ·
          refine ⟨17877377087806732834149845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11918251391871155222766563 17877377087806732834149845)
          ·
            refine ⟨419001025495470300800387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 17877377087806732834149845 419001025495470300800387)
            ·
              refine ⟨628501538243205451200581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419001025495470300800387 628501538243205451200581)
              ·
                refine ⟨117844038420601022100109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 628501538243205451200581 117844038420601022100109)
                ·
                  refine ⟨44191514407725383287541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117844038420601022100109 44191514407725383287541)
                  ·
                    rfl

theorem cell21_193641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4, 3].length) (baseStart_193641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_193641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_193641 prefixEnd_193641 := by exact prefixLift 193641
  have htrace : WordTrace (prefixWord ++ tailWord_193641) baseStart_193641 baseEnd_193641 := by
    simpa [prefixWord, tailWord_193641, baseEnd_193641] using wordTrace_append hprefix tailTrace_193641
  have hstable : (prefixWord ++ tailWord_193641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193641).length < 2 ^ (prefixWord ++ tailWord_193641).sum := by decide
  have hdescent : baseEnd_193641 < baseStart_193641 := by decide
  rcases family_descends (prefixWord ++ tailWord_193641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193700 : List Nat := [2, 3, 1, 2, 3, 1, 1, 3, 5]
def baseStart_193700 : Nat := 118140960795 + 193700 * 2 ^ 59
def prefixEnd_193700 : Nat := 4983230072969 + 3 ^ 40 * 193700 * 2
def baseEnd_193700 : Nat := 44204979011554391804087

theorem tailTrace_193700 : CollatzResearch.WordTrace tailWord_193700 prefixEnd_193700 44204979011554391804087 := by
  unfold tailWord_193700
  simp only [CollatzResearch.WordTrace]
  refine ⟨3532409699132728085685277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4709879598843637447580369 3532409699132728085685277)
  ·
    refine ⟨1324653637174773032131979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3532409699132728085685277 1324653637174773032131979)
    ·
      refine ⟨1986980455762159548197969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1324653637174773032131979 1986980455762159548197969)
      ·
        refine ⟨1490235341821619661148477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1986980455762159548197969 1490235341821619661148477)
        ·
          refine ⟨558838253183107372930679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1490235341821619661148477 558838253183107372930679)
          ·
            refine ⟨838257379774661059396019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558838253183107372930679 838257379774661059396019)
            ·
              refine ⟨1257386069661991589094029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 838257379774661059396019 1257386069661991589094029)
              ·
                refine ⟨471519776123246845910261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1257386069661991589094029 471519776123246845910261)
                ·
                  refine ⟨44204979011554391804087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 471519776123246845910261 44204979011554391804087)
                  ·
                    rfl

theorem cell21_193700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_193700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_193700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_193700 prefixEnd_193700 := by exact prefixLift 193700
  have htrace : WordTrace (prefixWord ++ tailWord_193700) baseStart_193700 baseEnd_193700 := by
    simpa [prefixWord, tailWord_193700, baseEnd_193700] using wordTrace_append hprefix tailTrace_193700
  have hstable : (prefixWord ++ tailWord_193700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193700).length < 2 ^ (prefixWord ++ tailWord_193700).sum := by decide
  have hdescent : baseEnd_193700 < baseStart_193700 := by decide
  rcases family_descends (prefixWord ++ tailWord_193700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193765 : List Nat := [1, 3, 1, 4, 3, 2, 2, 1, 4]
def baseStart_193765 : Nat := 118140960795 + 193765 * 2 ^ 59
def prefixEnd_193765 : Nat := 4983230072969 + 3 ^ 40 * 193765 * 2
def baseEnd_193765 : Nat := 44219812897128723220621

theorem tailTrace_193765 : CollatzResearch.WordTrace tailWord_193765 prefixEnd_193765 44219812897128723220621 := by
  unfold tailWord_193765
  simp only [CollatzResearch.WordTrace]
  refine ⟨7067190143029972272486749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4711460095353314848324499 7067190143029972272486749)
  ·
    refine ⟨2650196303636239602182531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7067190143029972272486749 2650196303636239602182531)
    ·
      refine ⟨3975294455454359403273797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2650196303636239602182531 3975294455454359403273797)
      ·
        refine ⟨745367710397692388113837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3975294455454359403273797 745367710397692388113837)
        ·
          refine ⟨279512891399134645542689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 745367710397692388113837 279512891399134645542689)
          ·
            refine ⟨209634668549350984157017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279512891399134645542689 209634668549350984157017)
            ·
              refine ⟨157226001412013238117763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209634668549350984157017 157226001412013238117763)
              ·
                refine ⟨235839002118019857176645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157226001412013238117763 235839002118019857176645)
                ·
                  refine ⟨44219812897128723220621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 235839002118019857176645 44219812897128723220621)
                  ·
                    rfl

theorem cell21_193765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_193765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_193765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_193765 prefixEnd_193765 := by exact prefixLift 193765
  have htrace : WordTrace (prefixWord ++ tailWord_193765) baseStart_193765 baseEnd_193765 := by
    simpa [prefixWord, tailWord_193765, baseEnd_193765] using wordTrace_append hprefix tailTrace_193765
  have hstable : (prefixWord ++ tailWord_193765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193765).length < 2 ^ (prefixWord ++ tailWord_193765).sum := by decide
  have hdescent : baseEnd_193765 < baseStart_193765 := by decide
  rcases family_descends (prefixWord ++ tailWord_193765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193804 : List Nat := [2, 2, 1, 2, 2, 12]
def baseStart_193804 : Nat := 118140960795 + 193804 * 2 ^ 59
def prefixEnd_193804 : Nat := 4983230072969 + 3 ^ 40 * 193804 * 2
def baseEnd_193804 : Nat := 1638100489943456372983

theorem tailTrace_193804 : CollatzResearch.WordTrace tailWord_193804 prefixEnd_193804 1638100489943456372983 := by
  unfold tailWord_193804
  simp only [CollatzResearch.WordTrace]
  refine ⟨3534306294944340966578233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4712408393259121288770977 3534306294944340966578233)
  ·
    refine ⟨2650729721208255724933675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3534306294944340966578233 2650729721208255724933675)
    ·
      refine ⟨3976094581812383587400513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2650729721208255724933675 3976094581812383587400513)
      ·
        refine ⟨2982070936359287690550385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3976094581812383587400513 2982070936359287690550385)
        ·
          refine ⟨2236553202269465767912789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2982070936359287690550385 2236553202269465767912789)
          ·
            refine ⟨1638100489943456372983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2236553202269465767912789 1638100489943456372983)
            ·
              rfl

theorem cell21_193804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 12].length) (baseStart_193804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_193804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_193804 prefixEnd_193804 := by exact prefixLift 193804
  have htrace : WordTrace (prefixWord ++ tailWord_193804) baseStart_193804 baseEnd_193804 := by
    simpa [prefixWord, tailWord_193804, baseEnd_193804] using wordTrace_append hprefix tailTrace_193804
  have hstable : (prefixWord ++ tailWord_193804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193804).length < 2 ^ (prefixWord ++ tailWord_193804).sum := by decide
  have hdescent : baseEnd_193804 < baseStart_193804 := by decide
  rcases family_descends (prefixWord ++ tailWord_193804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193880 : List Nat := [2, 1, 2, 2, 1, 1, 4, 8]
def baseStart_193880 : Nat := 118140960795 + 193880 * 2 ^ 59
def prefixEnd_193880 : Nat := 4983230072969 + 3 ^ 40 * 193880 * 2
def baseEnd_193880 : Nat := 14748685821304692934573

theorem tailTrace_193880 : CollatzResearch.WordTrace tailWord_193880 prefixEnd_193880 14748685821304692934573 := by
  unfold tailWord_193880
  simp only [CollatzResearch.WordTrace]
  refine ⟨3535692268806673456461547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4714256358408897941948729 3535692268806673456461547)
  ·
    refine ⟨5303538403210010184692321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3535692268806673456461547 5303538403210010184692321)
    ·
      refine ⟨3977653802407507638519241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5303538403210010184692321 3977653802407507638519241)
      ·
        refine ⟨2983240351805630728889431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3977653802407507638519241 2983240351805630728889431)
        ·
          refine ⟨4474860527708446093334147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2983240351805630728889431 4474860527708446093334147)
          ·
            refine ⟨6712290791562669140001221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4474860527708446093334147 6712290791562669140001221)
            ·
              refine ⟨1258554523418000463750229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6712290791562669140001221 1258554523418000463750229)
              ·
                refine ⟨14748685821304692934573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1258554523418000463750229 14748685821304692934573)
                ·
                  rfl

theorem cell21_193880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 8].length) (baseStart_193880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_193880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_193880 prefixEnd_193880 := by exact prefixLift 193880
  have htrace : WordTrace (prefixWord ++ tailWord_193880) baseStart_193880 baseEnd_193880 := by
    simpa [prefixWord, tailWord_193880, baseEnd_193880] using wordTrace_append hprefix tailTrace_193880
  have hstable : (prefixWord ++ tailWord_193880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193880).length < 2 ^ (prefixWord ++ tailWord_193880).sum := by decide
  have hdescent : baseEnd_193880 < baseStart_193880 := by decide
  rcases family_descends (prefixWord ++ tailWord_193880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193928 : List Nat := [2, 1, 3, 3, 1, 2, 3, 1, 5]
def baseStart_193928 : Nat := 118140960795 + 193928 * 2 ^ 59
def prefixEnd_193928 : Nat := 4983230072969 + 3 ^ 40 * 193928 * 2
def baseEnd_193928 : Nat := 44257011717876662003621

theorem tailTrace_193928 : CollatzResearch.WordTrace tailWord_193928 prefixEnd_193928 44257011717876662003621 := by
  unfold tailWord_193928
  simp only [CollatzResearch.WordTrace]
  refine ⟨3536567620719725555335219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4715423494292967407113625 3536567620719725555335219)
  ·
    refine ⟨5304851431079588333002829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3536567620719725555335219 5304851431079588333002829)
    ·
      refine ⟨1989319286654845624876061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5304851431079588333002829 1989319286654845624876061)
      ·
        refine ⟨745994732495567109328523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1989319286654845624876061 745994732495567109328523)
        ·
          refine ⟨1118992098743350663992785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745994732495567109328523 1118992098743350663992785)
          ·
            refine ⟨839244074057512997994589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1118992098743350663992785 839244074057512997994589)
            ·
              refine ⟨314716527771567374247971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 839244074057512997994589 314716527771567374247971)
              ·
                refine ⟨472074791657351061371957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314716527771567374247971 472074791657351061371957)
                ·
                  refine ⟨44257011717876662003621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 472074791657351061371957 44257011717876662003621)
                  ·
                    rfl

theorem cell21_193928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 5].length) (baseStart_193928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_193928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_193928 prefixEnd_193928 := by exact prefixLift 193928
  have htrace : WordTrace (prefixWord ++ tailWord_193928) baseStart_193928 baseEnd_193928 := by
    simpa [prefixWord, tailWord_193928, baseEnd_193928] using wordTrace_append hprefix tailTrace_193928
  have hstable : (prefixWord ++ tailWord_193928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193928).length < 2 ^ (prefixWord ++ tailWord_193928).sum := by decide
  have hdescent : baseEnd_193928 < baseStart_193928 := by decide
  rcases family_descends (prefixWord ++ tailWord_193928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193934 : List Nat := [4, 1, 1, 4, 3, 1, 2, 1, 4]
def baseStart_193934 : Nat := 118140960795 + 193934 * 2 ^ 59
def prefixEnd_193934 : Nat := 4983230072969 + 3 ^ 40 * 193934 * 2
def baseEnd_193934 : Nat := 44258380999621984903609

theorem tailTrace_193934 : CollatzResearch.WordTrace tailWord_193934 prefixEnd_193934 44258380999621984903609 := by
  unfold tailWord_193934
  simp only [CollatzResearch.WordTrace]
  refine ⟨884169259927214266923607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4715569386278476090259237 884169259927214266923607)
  ·
    refine ⟨1326253889890821400385411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 884169259927214266923607 1326253889890821400385411)
    ·
      refine ⟨1989380834836232100578117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1326253889890821400385411 1989380834836232100578117)
      ·
        refine ⟨373008906531793518858397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1989380834836232100578117 373008906531793518858397)
        ·
          refine ⟨139878339949422569571899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 373008906531793518858397 139878339949422569571899)
          ·
            refine ⟨209817509924133854357849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139878339949422569571899 209817509924133854357849)
            ·
              refine ⟨157363132443100390768387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209817509924133854357849 157363132443100390768387)
              ·
                refine ⟨236044698664650586152581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157363132443100390768387 236044698664650586152581)
                ·
                  refine ⟨44258380999621984903609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 236044698664650586152581 44258380999621984903609)
                  ·
                    rfl

theorem cell21_193934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_193934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_193934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_193934 prefixEnd_193934 := by exact prefixLift 193934
  have htrace : WordTrace (prefixWord ++ tailWord_193934) baseStart_193934 baseEnd_193934 := by
    simpa [prefixWord, tailWord_193934, baseEnd_193934] using wordTrace_append hprefix tailTrace_193934
  have hstable : (prefixWord ++ tailWord_193934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193934).length < 2 ^ (prefixWord ++ tailWord_193934).sum := by decide
  have hdescent : baseEnd_193934 < baseStart_193934 := by decide
  rcases family_descends (prefixWord ++ tailWord_193934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194001 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 10]
def baseStart_194001 : Nat := 118140960795 + 194001 * 2 ^ 59
def prefixEnd_194001 : Nat := 4983230072969 + 3 ^ 40 * 194001 * 2
def baseEnd_194001 : Nat := 44273671312444757286805

theorem tailTrace_194001 : CollatzResearch.WordTrace tailWord_194001 prefixEnd_194001 44273671312444757286805 := by
  unfold tailWord_194001
  simp only [CollatzResearch.WordTrace]
  refine ⟨7075797770174984578077857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4717198513449989718718571 7075797770174984578077857)
  ·
    refine ⟨5306848327631238433558393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7075797770174984578077857 5306848327631238433558393)
    ·
      refine ⟨3980136245723428825168795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5306848327631238433558393 3980136245723428825168795)
      ·
        refine ⟨5970204368585143237753193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3980136245723428825168795 5970204368585143237753193)
        ·
          refine ⟨4477653276438857428314895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5970204368585143237753193 4477653276438857428314895)
          ·
            refine ⟨6716479914658286142472343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4477653276438857428314895 6716479914658286142472343)
            ·
              refine ⟨10074719871987429213708515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6716479914658286142472343 10074719871987429213708515)
              ·
                refine ⟨15112079807981143820562773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10074719871987429213708515 15112079807981143820562773)
                ·
                  refine ⟨44273671312444757286805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 15112079807981143820562773 44273671312444757286805)
                  ·
                    rfl

theorem cell21_194001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_194001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_194001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_194001 prefixEnd_194001 := by exact prefixLift 194001
  have htrace : WordTrace (prefixWord ++ tailWord_194001) baseStart_194001 baseEnd_194001 := by
    simpa [prefixWord, tailWord_194001, baseEnd_194001] using wordTrace_append hprefix tailTrace_194001
  have hstable : (prefixWord ++ tailWord_194001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194001).length < 2 ^ (prefixWord ++ tailWord_194001).sum := by decide
  have hdescent : baseEnd_194001 < baseStart_194001 := by decide
  rcases family_descends (prefixWord ++ tailWord_194001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194021 : List Nat := [1, 3, 1, 5, 1, 1, 1, 5, 3]
def baseStart_194021 : Nat := 118140960795 + 194021 * 2 ^ 59
def prefixEnd_194021 : Nat := 4983230072969 + 3 ^ 40 * 194021 * 2
def baseEnd_194021 : Nat := 44278235584929166953431

theorem tailTrace_194021 : CollatzResearch.WordTrace tailWord_194021 prefixEnd_194021 44278235584929166953431 := by
  unfold tailWord_194021
  simp only [CollatzResearch.WordTrace]
  refine ⟨7076527230102527993805917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4717684820068351995870611 7076527230102527993805917)
  ·
    refine ⟨2653697711288447997677219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7076527230102527993805917 2653697711288447997677219)
    ·
      refine ⟨3980546566932671996515829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2653697711288447997677219 3980546566932671996515829)
      ·
        refine ⟨373176240649937999673359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3980546566932671996515829 373176240649937999673359)
        ·
          refine ⟨559764360974906999510039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373176240649937999673359 559764360974906999510039)
          ·
            refine ⟨839646541462360499265059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559764360974906999510039 839646541462360499265059)
            ·
              refine ⟨1259469812193540748897589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 839646541462360499265059 1259469812193540748897589)
              ·
                refine ⟨118075294893144445209149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1259469812193540748897589 118075294893144445209149)
                ·
                  refine ⟨44278235584929166953431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118075294893144445209149 44278235584929166953431)
                  ·
                    rfl

theorem cell21_194021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 3].length) (baseStart_194021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_194021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_194021 prefixEnd_194021 := by exact prefixLift 194021
  have htrace : WordTrace (prefixWord ++ tailWord_194021) baseStart_194021 baseEnd_194021 := by
    simpa [prefixWord, tailWord_194021, baseEnd_194021] using wordTrace_append hprefix tailTrace_194021
  have hstable : (prefixWord ++ tailWord_194021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194021).length < 2 ^ (prefixWord ++ tailWord_194021).sum := by decide
  have hdescent : baseEnd_194021 < baseStart_194021 := by decide
  rcases family_descends (prefixWord ++ tailWord_194021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194032 : List Nat := [2, 1, 1, 1, 3, 5, 8]
def baseStart_194032 : Nat := 118140960795 + 194032 * 2 ^ 59
def prefixEnd_194032 : Nat := 4983230072969 + 3 ^ 40 * 194032 * 2
def baseEnd_194032 : Nat := 4920082881643954696675

theorem tailTrace_194032 : CollatzResearch.WordTrace tailWord_194032 prefixEnd_194032 4920082881643954696675 := by
  unfold tailWord_194032
  simp only [CollatzResearch.WordTrace]
  refine ⟨3538464216531338436228175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4717952288708451248304233 3538464216531338436228175)
  ·
    refine ⟨5307696324797007654342263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3538464216531338436228175 5307696324797007654342263)
    ·
      refine ⟨7961544487195511481513395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5307696324797007654342263 7961544487195511481513395)
      ·
        refine ⟨11942316730793267222270093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7961544487195511481513395 11942316730793267222270093)
        ·
          refine ⟨4478368774047475208351285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11942316730793267222270093 4478368774047475208351285)
          ·
            refine ⟨419847072566950800782933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4478368774047475208351285 419847072566950800782933)
            ·
              refine ⟨4920082881643954696675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 419847072566950800782933 4920082881643954696675)
              ·
                rfl

theorem cell21_194032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 8].length) (baseStart_194032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_194032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_194032 prefixEnd_194032 := by exact prefixLift 194032
  have htrace : WordTrace (prefixWord ++ tailWord_194032) baseStart_194032 baseEnd_194032 := by
    simpa [prefixWord, tailWord_194032, baseEnd_194032] using wordTrace_append hprefix tailTrace_194032
  have hstable : (prefixWord ++ tailWord_194032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194032).length < 2 ^ (prefixWord ++ tailWord_194032).sum := by decide
  have hdescent : baseEnd_194032 < baseStart_194032 := by decide
  rcases family_descends (prefixWord ++ tailWord_194032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194111 : List Nat := [1, 1, 2, 2, 3, 3, 4, 1, 4]
def baseStart_194111 : Nat := 118140960795 + 194111 * 2 ^ 59
def prefixEnd_194111 : Nat := 4983230072969 + 3 ^ 40 * 194111 * 2
def baseEnd_194111 : Nat := 44298774811109010453247

theorem tailTrace_194111 : CollatzResearch.WordTrace tailWord_194111 prefixEnd_194111 44298774811109010453247 := by
  unfold tailWord_194111
  simp only [CollatzResearch.WordTrace]
  refine ⟨7079809799776473364582187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4719873199850982243054791 7079809799776473364582187)
  ·
    refine ⟨10619714699664710046873281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7079809799776473364582187 10619714699664710046873281)
    ·
      refine ⟨7964786024748532535154961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10619714699664710046873281 7964786024748532535154961)
      ·
        refine ⟨5973589518561399401366221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7964786024748532535154961 5973589518561399401366221)
        ·
          refine ⟨2240096069460524775512333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5973589518561399401366221 2240096069460524775512333)
          ·
            refine ⟨840036026047696790817125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2240096069460524775512333 840036026047696790817125)
            ·
              refine ⟨157506754883943148278211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 840036026047696790817125 157506754883943148278211)
              ·
                refine ⟨236260132325914722417317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157506754883943148278211 236260132325914722417317)
                ·
                  refine ⟨44298774811109010453247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 236260132325914722417317 44298774811109010453247)
                  ·
                    rfl

theorem cell21_194111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 4].length) (baseStart_194111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_194111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_194111 prefixEnd_194111 := by exact prefixLift 194111
  have htrace : WordTrace (prefixWord ++ tailWord_194111) baseStart_194111 baseEnd_194111 := by
    simpa [prefixWord, tailWord_194111, baseEnd_194111] using wordTrace_append hprefix tailTrace_194111
  have hstable : (prefixWord ++ tailWord_194111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194111).length < 2 ^ (prefixWord ++ tailWord_194111).sum := by decide
  have hdescent : baseEnd_194111 < baseStart_194111 := by decide
  rcases family_descends (prefixWord ++ tailWord_194111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194153 : List Nat := [1, 2, 1, 1, 1, 4, 2, 3, 6]
def baseStart_194153 : Nat := 118140960795 + 194153 * 2 ^ 59
def prefixEnd_194153 : Nat := 4983230072969 + 3 ^ 40 * 194153 * 2
def baseEnd_194153 : Nat := 44308359783326270753161

theorem tailTrace_194153 : CollatzResearch.WordTrace tailWord_194153 prefixEnd_194153 44308359783326270753161 := by
  unfold tailWord_194153
  simp only [CollatzResearch.WordTrace]
  refine ⟨7081341665624314537611113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4720894443749543025074075 7081341665624314537611113)
  ·
    refine ⟨5311006249218235903208335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7081341665624314537611113 5311006249218235903208335)
    ·
      refine ⟨7966509373827353854812503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5311006249218235903208335 7966509373827353854812503)
      ·
        refine ⟨11949764060741030782218755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7966509373827353854812503 11949764060741030782218755)
        ·
          refine ⟨17924646091111546173328133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11949764060741030782218755 17924646091111546173328133)
          ·
            refine ⟨3360871142083414907499025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17924646091111546173328133 3360871142083414907499025)
            ·
              refine ⟨2520653356562561180624269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3360871142083414907499025 2520653356562561180624269)
              ·
                refine ⟨945245008710960442734101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2520653356562561180624269 945245008710960442734101)
                ·
                  refine ⟨44308359783326270753161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 945245008710960442734101 44308359783326270753161)
                  ·
                    rfl

theorem cell21_194153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 6].length) (baseStart_194153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_194153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_194153 prefixEnd_194153 := by exact prefixLift 194153
  have htrace : WordTrace (prefixWord ++ tailWord_194153) baseStart_194153 baseEnd_194153 := by
    simpa [prefixWord, tailWord_194153, baseEnd_194153] using wordTrace_append hprefix tailTrace_194153
  have hstable : (prefixWord ++ tailWord_194153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194153).length < 2 ^ (prefixWord ++ tailWord_194153).sum := by decide
  have hdescent : baseEnd_194153 < baseStart_194153 := by decide
  rcases family_descends (prefixWord ++ tailWord_194153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194204 : List Nat := [2, 2, 3, 2, 3, 2, 1, 2, 4]
def baseStart_194204 : Nat := 118140960795 + 194204 * 2 ^ 59
def prefixEnd_194204 : Nat := 4983230072969 + 3 ^ 40 * 194204 * 2
def baseEnd_194204 : Nat := 44319998678161515403057

theorem tailTrace_194204 : CollatzResearch.WordTrace tailWord_194204 prefixEnd_194204 44319998678161515403057 := by
  unfold tailWord_194204
  simp only [CollatzResearch.WordTrace]
  refine ⟨3541600894219775123858833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4722134525626366831811777 3541600894219775123858833)
  ·
    refine ⟨2656200670664831342894125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3541600894219775123858833 2656200670664831342894125)
    ·
      refine ⟨996075251499311753585297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2656200670664831342894125 996075251499311753585297)
      ·
        refine ⟨747056438624483815188973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 996075251499311753585297 747056438624483815188973)
        ·
          refine ⟨280146164484181430695865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 747056438624483815188973 280146164484181430695865)
          ·
            refine ⟨210109623363136073021899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280146164484181430695865 210109623363136073021899)
            ·
              refine ⟨315164435044704109532849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210109623363136073021899 315164435044704109532849)
              ·
                refine ⟨236373326283528082149637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 315164435044704109532849 236373326283528082149637)
                ·
                  refine ⟨44319998678161515403057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 236373326283528082149637 44319998678161515403057)
                  ·
                    rfl

theorem cell21_194204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_194204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_194204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_194204 prefixEnd_194204 := by exact prefixLift 194204
  have htrace : WordTrace (prefixWord ++ tailWord_194204) baseStart_194204 baseEnd_194204 := by
    simpa [prefixWord, tailWord_194204, baseEnd_194204] using wordTrace_append hprefix tailTrace_194204
  have hstable : (prefixWord ++ tailWord_194204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194204).length < 2 ^ (prefixWord ++ tailWord_194204).sum := by decide
  have hdescent : baseEnd_194204 < baseStart_194204 := by decide
  rcases family_descends (prefixWord ++ tailWord_194204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194280 : List Nat := [2, 1, 4, 1, 3, 3, 2, 1, 4]
def baseStart_194280 : Nat := 118140960795 + 194280 * 2 ^ 59
def prefixEnd_194280 : Nat := 4983230072969 + 3 ^ 40 * 194280 * 2
def baseEnd_194280 : Nat := 44337342913602272136235

theorem tailTrace_194280 : CollatzResearch.WordTrace tailWord_194280 prefixEnd_194280 44337342913602272136235 := by
  unfold tailWord_194280
  simp only [CollatzResearch.WordTrace]
  refine ⟨3542986868082107613742147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4723982490776143484989529 3542986868082107613742147)
  ·
    refine ⟨5314480302123161420613221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3542986868082107613742147 5314480302123161420613221)
    ·
      refine ⟨996465056648092766364979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5314480302123161420613221 996465056648092766364979)
      ·
        refine ⟨1494697584972139149547469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 996465056648092766364979 1494697584972139149547469)
        ·
          refine ⟨560511594364552181080301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1494697584972139149547469 560511594364552181080301)
          ·
            refine ⟨210191847886707067905113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 560511594364552181080301 210191847886707067905113)
            ·
              refine ⟨157643885915030300928835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210191847886707067905113 157643885915030300928835)
              ·
                refine ⟨236465828872545451393253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157643885915030300928835 236465828872545451393253)
                ·
                  refine ⟨44337342913602272136235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 236465828872545451393253 44337342913602272136235)
                  ·
                    rfl

theorem cell21_194280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 4].length) (baseStart_194280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_194280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_194280 prefixEnd_194280 := by exact prefixLift 194280
  have htrace : WordTrace (prefixWord ++ tailWord_194280) baseStart_194280 baseEnd_194280 := by
    simpa [prefixWord, tailWord_194280, baseEnd_194280] using wordTrace_append hprefix tailTrace_194280
  have hstable : (prefixWord ++ tailWord_194280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194280).length < 2 ^ (prefixWord ++ tailWord_194280).sum := by decide
  have hdescent : baseEnd_194280 < baseStart_194280 := by decide
  rcases family_descends (prefixWord ++ tailWord_194280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194305 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 8]
def baseStart_194305 : Nat := 118140960795 + 194305 * 2 ^ 59
def prefixEnd_194305 : Nat := 4983230072969 + 3 ^ 40 * 194305 * 2
def baseEnd_194305 : Nat := 44343048254207784219517

theorem tailTrace_194305 : CollatzResearch.WordTrace tailWord_194305 prefixEnd_194305 44343048254207784219517 := by
  unfold tailWord_194305
  simp only [CollatzResearch.WordTrace]
  refine ⟨7086885561073644497144369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4724590374049096331429579 7086885561073644497144369)
  ·
    refine ⟨5315164170805233372858277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7086885561073644497144369 5315164170805233372858277)
    ·
      refine ⟨996593282025981257410927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5315164170805233372858277 996593282025981257410927)
      ·
        refine ⟨1494889923038971886116391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 996593282025981257410927 1494889923038971886116391)
        ·
          refine ⟨2242334884558457829174587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1494889923038971886116391 2242334884558457829174587)
          ·
            refine ⟨3363502326837686743761881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2242334884558457829174587 3363502326837686743761881)
            ·
              refine ⟨2522626745128265057821411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3363502326837686743761881 2522626745128265057821411)
              ·
                refine ⟨3783940117692397586732117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2522626745128265057821411 3783940117692397586732117)
                ·
                  refine ⟨44343048254207784219517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3783940117692397586732117 44343048254207784219517)
                  ·
                    rfl

theorem cell21_194305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 8].length) (baseStart_194305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_194305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_194305 prefixEnd_194305 := by exact prefixLift 194305
  have htrace : WordTrace (prefixWord ++ tailWord_194305) baseStart_194305 baseEnd_194305 := by
    simpa [prefixWord, tailWord_194305, baseEnd_194305] using wordTrace_append hprefix tailTrace_194305
  have hstable : (prefixWord ++ tailWord_194305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194305).length < 2 ^ (prefixWord ++ tailWord_194305).sum := by decide
  have hdescent : baseEnd_194305 < baseStart_194305 := by decide
  rcases family_descends (prefixWord ++ tailWord_194305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194325 : List Nat := [1, 3, 2, 1, 2, 3, 4, 2, 3]
def baseStart_194325 : Nat := 118140960795 + 194325 * 2 ^ 59
def prefixEnd_194325 : Nat := 4983230072969 + 3 ^ 40 * 194325 * 2
def baseEnd_194325 : Nat := 44347612526692193886143

theorem tailTrace_194325 : CollatzResearch.WordTrace tailWord_194325 prefixEnd_194325 44347612526692193886143 := by
  unfold tailWord_194325
  simp only [CollatzResearch.WordTrace]
  refine ⟨7087615021001187912872429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4725076680667458608581619 7087615021001187912872429)
  ·
    refine ⟨2657855632875445467327161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7087615021001187912872429 2657855632875445467327161)
    ·
      refine ⟨1993391724656584100495371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2657855632875445467327161 1993391724656584100495371)
      ·
        refine ⟨2990087586984876150743057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1993391724656584100495371 2990087586984876150743057)
        ·
          refine ⟨2242565690238657113057293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2990087586984876150743057 2242565690238657113057293)
          ·
            refine ⟨840962133839496417396485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2242565690238657113057293 840962133839496417396485)
            ·
              refine ⟨157680400094905578261841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 840962133839496417396485 157680400094905578261841)
              ·
                refine ⟨118260300071179183696381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157680400094905578261841 118260300071179183696381)
                ·
                  refine ⟨44347612526692193886143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118260300071179183696381 44347612526692193886143)
                  ·
                    rfl

theorem cell21_194325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2, 3].length) (baseStart_194325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_194325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_194325 prefixEnd_194325 := by exact prefixLift 194325
  have htrace : WordTrace (prefixWord ++ tailWord_194325) baseStart_194325 baseEnd_194325 := by
    simpa [prefixWord, tailWord_194325, baseEnd_194325] using wordTrace_append hprefix tailTrace_194325
  have hstable : (prefixWord ++ tailWord_194325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194325).length < 2 ^ (prefixWord ++ tailWord_194325).sum := by decide
  have hdescent : baseEnd_194325 < baseStart_194325 := by decide
  rcases family_descends (prefixWord ++ tailWord_194325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194353 : List Nat := [1, 2, 2, 3, 2, 3, 3, 5]
def baseStart_194353 : Nat := 118140960795 + 194353 * 2 ^ 59
def prefixEnd_194353 : Nat := 4983230072969 + 3 ^ 40 * 194353 * 2
def baseEnd_194353 : Nat := 14784667502723455806473

theorem tailTrace_194353 : CollatzResearch.WordTrace tailWord_194353 prefixEnd_194353 14784667502723455806473 := by
  unfold tailWord_194353
  simp only [CollatzResearch.WordTrace]
  refine ⟨7088636264899748694891713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4725757509933165796594475 7088636264899748694891713)
  ·
    refine ⟨5316477198674811521168785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7088636264899748694891713 5316477198674811521168785)
    ·
      refine ⟨3987357899006108640876589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5316477198674811521168785 3987357899006108640876589)
      ·
        refine ⟨1495259212127290740328721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3987357899006108640876589 1495259212127290740328721)
        ·
          refine ⟨1121444409095468055246541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1495259212127290740328721 1121444409095468055246541)
          ·
            refine ⟨420541653410800520717453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1121444409095468055246541 420541653410800520717453)
            ·
              refine ⟨157703120029050195269045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 420541653410800520717453 157703120029050195269045)
              ·
                refine ⟨14784667502723455806473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157703120029050195269045 14784667502723455806473)
                ·
                  rfl

theorem cell21_194353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 5].length) (baseStart_194353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_194353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_194353 prefixEnd_194353 := by exact prefixLift 194353
  have htrace : WordTrace (prefixWord ++ tailWord_194353) baseStart_194353 baseEnd_194353 := by
    simpa [prefixWord, tailWord_194353, baseEnd_194353] using wordTrace_append hprefix tailTrace_194353
  have hstable : (prefixWord ++ tailWord_194353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194353).length < 2 ^ (prefixWord ++ tailWord_194353).sum := by decide
  have hdescent : baseEnd_194353 < baseStart_194353 := by decide
  rcases family_descends (prefixWord ++ tailWord_194353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194412 : List Nat := [2, 2, 1, 1, 4, 3, 1, 7]
def baseStart_194412 : Nat := 118140960795 + 194412 * 2 ^ 59
def prefixEnd_194412 : Nat := 4983230072969 + 3 ^ 40 * 194412 * 2
def baseEnd_194412 : Nat := 14789155703999791978655

theorem tailTrace_194412 : CollatzResearch.WordTrace tailWord_194412 prefixEnd_194412 14789155703999791978655 := by
  unfold tailWord_194412
  simp only [CollatzResearch.WordTrace]
  refine ⟨3545394085843000885644745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4727192114457334514192993 3545394085843000885644745)
  ·
    refine ⟨2659045564382250664233559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3545394085843000885644745 2659045564382250664233559)
    ·
      refine ⟨3988568346573375996350339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2659045564382250664233559 3988568346573375996350339)
      ·
        refine ⟨5982852519860063994525509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3988568346573375996350339 5982852519860063994525509)
        ·
          refine ⟨1121784847473761998973533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5982852519860063994525509 1121784847473761998973533)
          ·
            refine ⟨420669317802660749615075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1121784847473761998973533 420669317802660749615075)
            ·
              refine ⟨631003976703991124422613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420669317802660749615075 631003976703991124422613)
              ·
                refine ⟨14789155703999791978655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 631003976703991124422613 14789155703999791978655)
                ·
                  rfl

theorem cell21_194412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 7].length) (baseStart_194412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_194412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_194412 prefixEnd_194412 := by exact prefixLift 194412
  have htrace : WordTrace (prefixWord ++ tailWord_194412) baseStart_194412 baseEnd_194412 := by
    simpa [prefixWord, tailWord_194412, baseEnd_194412] using wordTrace_append hprefix tailTrace_194412
  have hstable : (prefixWord ++ tailWord_194412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194412).length < 2 ^ (prefixWord ++ tailWord_194412).sum := by decide
  have hdescent : baseEnd_194412 < baseStart_194412 := by decide
  rcases family_descends (prefixWord ++ tailWord_194412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194426 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 7]
def baseStart_194426 : Nat := 118140960795 + 194426 * 2 ^ 59
def prefixEnd_194426 : Nat := 4983230072969 + 3 ^ 40 * 194426 * 2
def baseEnd_194426 : Nat := 44370662102738462702603

theorem tailTrace_194426 : CollatzResearch.WordTrace tailWord_194426 prefixEnd_194426 44370662102738462702603 := by
  unfold tailWord_194426
  simp only [CollatzResearch.WordTrace]
  refine ⟨1772824698408820540574783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4727532529090188108199421 1772824698408820540574783)
  ·
    refine ⟨2659237047613230810862175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1772824698408820540574783 2659237047613230810862175)
    ·
      refine ⟨3988855571419846216293263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2659237047613230810862175 3988855571419846216293263)
      ·
        refine ⟨5983283357129769324439895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3988855571419846216293263 5983283357129769324439895)
        ·
          refine ⟨8974925035694653986659843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5983283357129769324439895 8974925035694653986659843)
          ·
            refine ⟨13462387553541980979989765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8974925035694653986659843 13462387553541980979989765)
            ·
              refine ⟨2524197666289121433748081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13462387553541980979989765 2524197666289121433748081)
              ·
                refine ⟨1893148249716841075311061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2524197666289121433748081 1893148249716841075311061)
                ·
                  refine ⟨44370662102738462702603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1893148249716841075311061 44370662102738462702603)
                  ·
                    rfl

theorem cell21_194426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_194426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_194426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_194426 prefixEnd_194426 := by exact prefixLift 194426
  have htrace : WordTrace (prefixWord ++ tailWord_194426) baseStart_194426 baseEnd_194426 := by
    simpa [prefixWord, tailWord_194426, baseEnd_194426] using wordTrace_append hprefix tailTrace_194426
  have hstable : (prefixWord ++ tailWord_194426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194426).length < 2 ^ (prefixWord ++ tailWord_194426).sum := by decide
  have hdescent : baseEnd_194426 < baseStart_194426 := by decide
  rcases family_descends (prefixWord ++ tailWord_194426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194446 : List Nat := [4, 1, 1, 5, 1, 1, 2, 6]
def baseStart_194446 : Nat := 118140960795 + 194446 * 2 ^ 59
def prefixEnd_194446 : Nat := 4983230072969 + 3 ^ 40 * 194446 * 2
def baseEnd_194446 : Nat := 14791742125074290789743

theorem tailTrace_194446 : CollatzResearch.WordTrace tailWord_194446 prefixEnd_194446 14791742125074290789743 := by
  unfold tailWord_194446
  simp only [CollatzResearch.WordTrace]
  refine ⟨886503531695353197253399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4728018835708550385351461 886503531695353197253399)
  ·
    refine ⟨1329755297543029795880099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 886503531695353197253399 1329755297543029795880099)
    ·
      refine ⟨1994632946314544693820149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1329755297543029795880099 1994632946314544693820149)
      ·
        refine ⟨186996838716988565045639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1994632946314544693820149 186996838716988565045639)
        ·
          refine ⟨280495258075482847568459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186996838716988565045639 280495258075482847568459)
          ·
            refine ⟨420742887113224271352689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280495258075482847568459 420742887113224271352689)
            ·
              refine ⟨315557165334918203514517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420742887113224271352689 315557165334918203514517)
              ·
                refine ⟨14791742125074290789743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 315557165334918203514517 14791742125074290789743)
                ·
                  rfl

theorem cell21_194446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_194446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_194446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_194446 prefixEnd_194446 := by exact prefixLift 194446
  have htrace : WordTrace (prefixWord ++ tailWord_194446) baseStart_194446 baseEnd_194446 := by
    simpa [prefixWord, tailWord_194446, baseEnd_194446] using wordTrace_append hprefix tailTrace_194446
  have hstable : (prefixWord ++ tailWord_194446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194446).length < 2 ^ (prefixWord ++ tailWord_194446).sum := by decide
  have hdescent : baseEnd_194446 < baseStart_194446 := by decide
  rcases family_descends (prefixWord ++ tailWord_194446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194494 : List Nat := [4, 2, 1, 1, 1, 5, 2, 2, 3]
def baseStart_194494 : Nat := 118140960795 + 194494 * 2 ^ 59
def prefixEnd_194494 : Nat := 4983230072969 + 3 ^ 40 * 194494 * 2
def baseEnd_194494 : Nat := 44386180629185455569131

theorem tailTrace_194494 : CollatzResearch.WordTrace tailWord_194494 prefixEnd_194494 44386180629185455569131 := by
  unfold tailWord_194494
  simp only [CollatzResearch.WordTrace]
  refine ⟨886722369673616221971817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4729185971592619850516357 886722369673616221971817)
  ·
    refine ⟨665041777255212166478863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 886722369673616221971817 665041777255212166478863)
    ·
      refine ⟨997562665882818249718295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 665041777255212166478863 997562665882818249718295)
      ·
        refine ⟨1496343998824227374577443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 997562665882818249718295 1496343998824227374577443)
        ·
          refine ⟨2244515998236341061866165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1496343998824227374577443 2244515998236341061866165)
          ·
            refine ⟨210423374834656974549953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2244515998236341061866165 210423374834656974549953)
            ·
              refine ⟨157817531125992730912465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210423374834656974549953 157817531125992730912465)
              ·
                refine ⟨118363148344494548184349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157817531125992730912465 118363148344494548184349)
                ·
                  refine ⟨44386180629185455569131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118363148344494548184349 44386180629185455569131)
                  ·
                    rfl

theorem cell21_194494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_194494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_194494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_194494 prefixEnd_194494 := by exact prefixLift 194494
  have htrace : WordTrace (prefixWord ++ tailWord_194494) baseStart_194494 baseEnd_194494 := by
    simpa [prefixWord, tailWord_194494, baseEnd_194494] using wordTrace_append hprefix tailTrace_194494
  have hstable : (prefixWord ++ tailWord_194494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194494).length < 2 ^ (prefixWord ++ tailWord_194494).sum := by decide
  have hdescent : baseEnd_194494 < baseStart_194494 := by decide
  rcases family_descends (prefixWord ++ tailWord_194494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194567 : List Nat := [1, 1, 4, 3, 1, 3, 3, 1, 4]
def baseStart_194567 : Nat := 118140960795 + 194567 * 2 ^ 59
def prefixEnd_194567 : Nat := 4983230072969 + 3 ^ 40 * 194567 * 2
def baseEnd_194567 : Nat := 44402840223753550852315

theorem tailTrace_194567 : CollatzResearch.WordTrace tailWord_194567 prefixEnd_194567 44402840223753550852315 := by
  unfold tailWord_194567
  simp only [CollatzResearch.WordTrace]
  refine ⟨7096441486124463243181955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4730960990749642162121303 7096441486124463243181955)
  ·
    refine ⟨10644662229186694864772933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7096441486124463243181955 10644662229186694864772933)
    ·
      refine ⟨1995874167972505287144925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10644662229186694864772933 1995874167972505287144925)
      ·
        refine ⟨748452812989689482679347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1995874167972505287144925 748452812989689482679347)
        ·
          refine ⟨1122679219484534224019021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 748452812989689482679347 1122679219484534224019021)
          ·
            refine ⟨421004707306700334007133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1122679219484534224019021 421004707306700334007133)
            ·
              refine ⟨157876765240012625252675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 421004707306700334007133 157876765240012625252675)
              ·
                refine ⟨236815147860018937879013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157876765240012625252675 236815147860018937879013)
                ·
                  refine ⟨44402840223753550852315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 236815147860018937879013 44402840223753550852315)
                  ·
                    rfl

theorem cell21_194567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 4].length) (baseStart_194567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_194567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_194567 prefixEnd_194567 := by exact prefixLift 194567
  have htrace : WordTrace (prefixWord ++ tailWord_194567) baseStart_194567 baseEnd_194567 := by
    simpa [prefixWord, tailWord_194567, baseEnd_194567] using wordTrace_append hprefix tailTrace_194567
  have hstable : (prefixWord ++ tailWord_194567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194567).length < 2 ^ (prefixWord ++ tailWord_194567).sum := by decide
  have hdescent : baseEnd_194567 < baseStart_194567 := by decide
  rcases family_descends (prefixWord ++ tailWord_194567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194573 : List Nat := [1, 7, 1, 2, 2, 1, 2, 5]
def baseStart_194573 : Nat := 118140960795 + 194573 * 2 ^ 59
def prefixEnd_194573 : Nat := 4983230072969 + 3 ^ 40 * 194573 * 2
def baseEnd_194573 : Nat := 14801403168499624584101

theorem tailTrace_194573 : CollatzResearch.WordTrace tailWord_194573 prefixEnd_194573 14801403168499624584101 := by
  unfold tailWord_194573
  simp only [CollatzResearch.WordTrace]
  refine ⟨7096660324102726267900373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4731106882735150845266915 7096660324102726267900373)
  ·
    refine ⟨166327976346157646903915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 7096660324102726267900373 166327976346157646903915)
    ·
      refine ⟨249491964519236470355873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166327976346157646903915 249491964519236470355873)
      ·
        refine ⟨187118973389427352766905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249491964519236470355873 187118973389427352766905)
        ·
          refine ⟨140339230042070514575179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187118973389427352766905 140339230042070514575179)
          ·
            refine ⟨210508845063105771862769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140339230042070514575179 210508845063105771862769)
            ·
              refine ⟨157881633797329328897077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210508845063105771862769 157881633797329328897077)
              ·
                refine ⟨14801403168499624584101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157881633797329328897077 14801403168499624584101)
                ·
                  rfl

theorem cell21_194573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 5].length) (baseStart_194573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_194573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_194573 prefixEnd_194573 := by exact prefixLift 194573
  have htrace : WordTrace (prefixWord ++ tailWord_194573) baseStart_194573 baseEnd_194573 := by
    simpa [prefixWord, tailWord_194573, baseEnd_194573] using wordTrace_append hprefix tailTrace_194573
  have hstable : (prefixWord ++ tailWord_194573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194573).length < 2 ^ (prefixWord ++ tailWord_194573).sum := by decide
  have hdescent : baseEnd_194573 < baseStart_194573 := by decide
  rcases family_descends (prefixWord ++ tailWord_194573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194609 : List Nat := [1, 2, 2, 3, 1, 3, 2, 1, 6]
def baseStart_194609 : Nat := 118140960795 + 194609 * 2 ^ 59
def prefixEnd_194609 : Nat := 4983230072969 + 3 ^ 40 * 194609 * 2
def baseEnd_194609 : Nat := 44412425195970811152229

theorem tailTrace_194609 : CollatzResearch.WordTrace tailWord_194609 prefixEnd_194609 44412425195970811152229 := by
  unfold tailWord_194609
  simp only [CollatzResearch.WordTrace]
  refine ⟨7097973351972304416210881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4731982234648202944140587 7097973351972304416210881)
  ·
    refine ⟨5323480013979228312158161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7097973351972304416210881 5323480013979228312158161)
    ·
      refine ⟨3992610010484421234118621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5323480013979228312158161 3992610010484421234118621)
      ·
        refine ⟨1497228753931657962794483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3992610010484421234118621 1497228753931657962794483)
        ·
          refine ⟨2245843130897486944191725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1497228753931657962794483 2245843130897486944191725)
          ·
            refine ⟨842191174086557604071897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2245843130897486944191725 842191174086557604071897)
            ·
              refine ⟨631643380564918203053923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 842191174086557604071897 631643380564918203053923)
              ·
                refine ⟨947465070847377304580885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631643380564918203053923 947465070847377304580885)
                ·
                  refine ⟨44412425195970811152229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 947465070847377304580885 44412425195970811152229)
                  ·
                    rfl

theorem cell21_194609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 6].length) (baseStart_194609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_194609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_194609 prefixEnd_194609 := by exact prefixLift 194609
  have htrace : WordTrace (prefixWord ++ tailWord_194609) baseStart_194609 baseEnd_194609 := by
    simpa [prefixWord, tailWord_194609, baseEnd_194609] using wordTrace_append hprefix tailTrace_194609
  have hstable : (prefixWord ++ tailWord_194609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194609).length < 2 ^ (prefixWord ++ tailWord_194609).sum := by decide
  have hdescent : baseEnd_194609 < baseStart_194609 := by decide
  rcases family_descends (prefixWord ++ tailWord_194609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
