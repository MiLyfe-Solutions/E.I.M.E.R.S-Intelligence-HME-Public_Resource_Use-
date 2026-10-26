import V185TrunkScan23Chunk0467

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2768762 : List Nat := [3, 1, 1, 1, 1, 1, 6, 9]
def baseStart_2768762 : Nat := 118140960795 + 2768762 * 2 ^ 59
def prefixEnd_2768762 : Nat := 4983230072969 + 3 ^ 40 * 2768762 * 2
def baseEnd_2768762 : Nat := 52655767552000053320063

theorem tailTrace_2768762 : CollatzResearch.WordTrace tailWord_2768762 prefixEnd_2768762 52655767552000053320063 := by
  unfold tailWord_2768762
  simp only [CollatzResearch.WordTrace]
  refine ⟨25246261598813903936963135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67323364263503743831901693 25246261598813903936963135)
  ·
    refine ⟨37869392398220855905444703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25246261598813903936963135 37869392398220855905444703)
    ·
      refine ⟨56804088597331283858167055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37869392398220855905444703 56804088597331283858167055)
      ·
        refine ⟨85206132895996925787250583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56804088597331283858167055 85206132895996925787250583)
        ·
          refine ⟨127809199343995388680875875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85206132895996925787250583 127809199343995388680875875)
          ·
            refine ⟨191713799015993083021313813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127809199343995388680875875 191713799015993083021313813)
            ·
              refine ⟨8986584328874675766624085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 191713799015993083021313813 8986584328874675766624085)
              ·
                refine ⟨52655767552000053320063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8986584328874675766624085 52655767552000053320063)
                ·
                  rfl

theorem cell23_2768762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 9].length) (baseStart_2768762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768762 prefixEnd_2768762 := by exact prefixLift 2768762
  have htrace : WordTrace (prefixWord ++ tailWord_2768762) baseStart_2768762 baseEnd_2768762 := by
    simpa [prefixWord, tailWord_2768762, baseEnd_2768762] using wordTrace_append hprefix tailTrace_2768762
  have hstable : (prefixWord ++ tailWord_2768762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768762).length < 2 ^ (prefixWord ++ tailWord_2768762).sum := by decide
  have hdescent : baseEnd_2768762 < baseStart_2768762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768766 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 3, 6]
def baseStart_2768766 : Nat := 118140960795 + 2768766 * 2 ^ 59
def prefixEnd_2768766 : Nat := 4983230072969 + 3 ^ 40 * 2768766 * 2
def baseEnd_2768766 : Nat := 473902592608873141330561

theorem tailTrace_2768766 : CollatzResearch.WordTrace tailWord_2768766 prefixEnd_2768766 473902592608873141330561 := by
  unfold tailWord_2768766
  simp only [CollatzResearch.WordTrace]
  refine ⟨12623149035905140553874769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67323461524827416287332101 12623149035905140553874769)
  ·
    refine ⟨9467361776928855415406077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12623149035905140553874769 9467361776928855415406077)
    ·
      refine ⟨3550260666348320780777279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9467361776928855415406077 3550260666348320780777279)
      ·
        refine ⟨5325390999522481171165919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3550260666348320780777279 5325390999522481171165919)
        ·
          refine ⟨7988086499283721756748879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5325390999522481171165919 7988086499283721756748879)
          ·
            refine ⟨11982129748925582635123319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7988086499283721756748879 11982129748925582635123319)
            ·
              refine ⟨17973194623388373952684979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11982129748925582635123319 17973194623388373952684979)
              ·
                refine ⟨26959791935082560929027469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17973194623388373952684979 26959791935082560929027469)
                ·
                  refine ⟨10109921975655960348385301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26959791935082560929027469 10109921975655960348385301)
                  ·
                    refine ⟨473902592608873141330561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10109921975655960348385301 473902592608873141330561)
                    ·
                      rfl

theorem cell23_2768766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_2768766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768766 prefixEnd_2768766 := by exact prefixLift 2768766
  have htrace : WordTrace (prefixWord ++ tailWord_2768766) baseStart_2768766 baseEnd_2768766 := by
    simpa [prefixWord, tailWord_2768766, baseEnd_2768766] using wordTrace_append hprefix tailTrace_2768766
  have hstable : (prefixWord ++ tailWord_2768766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768766).length < 2 ^ (prefixWord ++ tailWord_2768766).sum := by decide
  have hdescent : baseEnd_2768766 < baseStart_2768766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768789 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 3, 3, 3]
def baseStart_2768789 : Nat := 118140960795 + 2768789 * 2 ^ 59
def prefixEnd_2768789 : Nat := 4983230072969 + 3 ^ 40 * 2768789 * 2
def baseEnd_2768789 : Nat := 1421719587881672834004077

theorem tailTrace_2768789 : CollatzResearch.WordTrace tailWord_2768789 prefixEnd_2768789 1421719587881672834004077 := by
  unfold tailWord_2768789
  simp only [CollatzResearch.WordTrace]
  refine ⟨100986031166157799359085421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67324020777438532906056947 100986031166157799359085421)
  ·
    refine ⟨37869761687309174759657033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100986031166157799359085421 37869761687309174759657033)
    ·
      refine ⟨28402321265481881069742775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37869761687309174759657033 28402321265481881069742775)
      ·
        refine ⟨42603481898222821604614163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28402321265481881069742775 42603481898222821604614163)
        ·
          refine ⟨63905222847334232406921245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42603481898222821604614163 63905222847334232406921245)
          ·
            refine ⟨23964458567750337152595467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63905222847334232406921245 23964458567750337152595467)
            ·
              refine ⟨35946687851625505728893201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23964458567750337152595467 35946687851625505728893201)
              ·
                refine ⟨26960015888719129296669901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35946687851625505728893201 26960015888719129296669901)
                ·
                  refine ⟨10110005958269673486251213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26960015888719129296669901 10110005958269673486251213)
                  ·
                    refine ⟨3791252234351127557344205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10110005958269673486251213 3791252234351127557344205)
                    ·
                      refine ⟨1421719587881672834004077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3791252234351127557344205 1421719587881672834004077)
                      ·
                        rfl

theorem cell23_2768789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_2768789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768789 prefixEnd_2768789 := by exact prefixLift 2768789
  have htrace : WordTrace (prefixWord ++ tailWord_2768789) baseStart_2768789 baseEnd_2768789 := by
    simpa [prefixWord, tailWord_2768789, baseEnd_2768789] using wordTrace_append hprefix tailTrace_2768789
  have hstable : (prefixWord ++ tailWord_2768789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768789).length < 2 ^ (prefixWord ++ tailWord_2768789).sum := by decide
  have hdescent : baseEnd_2768789 < baseStart_2768789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768796 : List Nat := [2, 2, 3, 3, 1, 3, 1, 8]
def baseStart_2768796 : Nat := 118140960795 + 2768796 * 2 ^ 59
def prefixEnd_2768796 : Nat := 4983230072969 + 3 ^ 40 * 2768796 * 2
def baseEnd_2768796 : Nat := 52656414157268678022835

theorem tailTrace_2768796 : CollatzResearch.WordTrace tailWord_2768796 prefixEnd_2768796 52656414157268678022835 := by
  unfold tailWord_2768796
  simp only [CollatzResearch.WordTrace]
  refine ⟨50493143238566219777295121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67324190984754959703060161 50493143238566219777295121)
  ·
    refine ⟨37869857428924664832971341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50493143238566219777295121 37869857428924664832971341)
    ·
      refine ⟨14201196535846749312364253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37869857428924664832971341 14201196535846749312364253)
      ·
        refine ⟨5325448700942530992136595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14201196535846749312364253 5325448700942530992136595)
        ·
          refine ⟨7988173051413796488204893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5325448700942530992136595 7988173051413796488204893)
          ·
            refine ⟨2995564894280173683076835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7988173051413796488204893 2995564894280173683076835)
            ·
              refine ⟨4493347341420260524615253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2995564894280173683076835 4493347341420260524615253)
              ·
                refine ⟨52656414157268678022835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4493347341420260524615253 52656414157268678022835)
                ·
                  rfl

theorem cell23_2768796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 8].length) (baseStart_2768796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768796 prefixEnd_2768796 := by exact prefixLift 2768796
  have htrace : WordTrace (prefixWord ++ tailWord_2768796) baseStart_2768796 baseEnd_2768796 := by
    simpa [prefixWord, tailWord_2768796, baseEnd_2768796] using wordTrace_append hprefix tailTrace_2768796
  have hstable : (prefixWord ++ tailWord_2768796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768796).length < 2 ^ (prefixWord ++ tailWord_2768796).sum := by decide
  have hdescent : baseEnd_2768796 < baseStart_2768796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768812 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 10]
def baseStart_2768812 : Nat := 118140960795 + 2768812 * 2 ^ 59
def prefixEnd_2768812 : Nat := 4983230072969 + 3 ^ 40 * 2768812 * 2
def baseEnd_2768812 : Nat := 1421731397936726244016471

theorem tailTrace_2768812 : CollatzResearch.WordTrace tailWord_2768812 prefixEnd_2768812 1421731397936726244016471 := by
  unfold tailWord_2768812
  simp only [CollatzResearch.WordTrace]
  refine ⟨50493435022537237143586345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67324580030049649524781793 50493435022537237143586345)
  ·
    refine ⟨37870076266902927857689759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50493435022537237143586345 37870076266902927857689759)
    ·
      refine ⟨56805114400354391786534639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37870076266902927857689759 56805114400354391786534639)
      ·
        refine ⟨85207671600531587679801959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56805114400354391786534639 85207671600531587679801959)
        ·
          refine ⟨127811507400797381519702939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85207671600531587679801959 127811507400797381519702939)
          ·
            refine ⟨191717261101196072279554409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127811507400797381519702939 191717261101196072279554409)
            ·
              refine ⟨143787945825897054209665807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191717261101196072279554409 143787945825897054209665807)
              ·
                refine ⟨215681918738845581314498711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143787945825897054209665807 215681918738845581314498711)
                ·
                  refine ⟨323522878108268371971748067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215681918738845581314498711 323522878108268371971748067)
                  ·
                    refine ⟨485284317162402557957622101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 323522878108268371971748067 485284317162402557957622101)
                    ·
                      refine ⟨1421731397936726244016471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 485284317162402557957622101 1421731397936726244016471)
                      ·
                        rfl

theorem cell23_2768812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_2768812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768812 prefixEnd_2768812 := by exact prefixLift 2768812
  have htrace : WordTrace (prefixWord ++ tailWord_2768812) baseStart_2768812 baseEnd_2768812 := by
    simpa [prefixWord, tailWord_2768812, baseEnd_2768812] using wordTrace_append hprefix tailTrace_2768812
  have hstable : (prefixWord ++ tailWord_2768812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768812).length < 2 ^ (prefixWord ++ tailWord_2768812).sum := by decide
  have hdescent : baseEnd_2768812 < baseStart_2768812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768840 : List Nat := [2, 1, 3, 1, 4, 3, 1, 2, 2, 1, 3]
def baseStart_2768840 : Nat := 118140960795 + 2768840 * 2 ^ 59
def prefixEnd_2768840 : Nat := 4983230072969 + 3 ^ 40 * 2768840 * 2
def baseEnd_2768840 : Nat := 1421745775395052134466343

theorem tailTrace_2768840 : CollatzResearch.WordTrace tailWord_2768840 prefixEnd_2768840 1421745775395052134466343 := by
  unfold tailWord_2768840
  simp only [CollatzResearch.WordTrace]
  refine ⟨50493945644486517534595987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67325260859315356712794649 50493945644486517534595987)
  ·
    refine ⟨75740918466729776301893981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50493945644486517534595987 75740918466729776301893981)
    ·
      refine ⟨28402844425023666113210243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75740918466729776301893981 28402844425023666113210243)
      ·
        refine ⟨42604266637535499169815365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28402844425023666113210243 42604266637535499169815365)
        ·
          refine ⟨7988299994537906094340381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42604266637535499169815365 7988299994537906094340381)
          ·
            refine ⟨2995612497951714785377643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7988299994537906094340381 2995612497951714785377643)
            ·
              refine ⟨4493418746927572178066465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2995612497951714785377643 4493418746927572178066465)
              ·
                refine ⟨3370064060195679133549849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4493418746927572178066465 3370064060195679133549849)
                ·
                  refine ⟨2527548045146759350162387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3370064060195679133549849 2527548045146759350162387)
                  ·
                    refine ⟨3791322067720139025243581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2527548045146759350162387 3791322067720139025243581)
                    ·
                      refine ⟨1421745775395052134466343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3791322067720139025243581 1421745775395052134466343)
                      ·
                        rfl

theorem cell23_2768840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_2768840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768840 prefixEnd_2768840 := by exact prefixLift 2768840
  have htrace : WordTrace (prefixWord ++ tailWord_2768840) baseStart_2768840 baseEnd_2768840 := by
    simpa [prefixWord, tailWord_2768840, baseEnd_2768840] using wordTrace_append hprefix tailTrace_2768840
  have hstable : (prefixWord ++ tailWord_2768840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768840).length < 2 ^ (prefixWord ++ tailWord_2768840).sum := by decide
  have hdescent : baseEnd_2768840 < baseStart_2768840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768849 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 2, 4, 3]
def baseStart_2768849 : Nat := 118140960795 + 2768849 * 2 ^ 59
def prefixEnd_2768849 : Nat := 4983230072969 + 3 ^ 40 * 2768849 * 2
def baseEnd_2768849 : Nat := 1421750396720942599253801

theorem tailTrace_2768849 : CollatzResearch.WordTrace tailWord_2768849 prefixEnd_2768849 1421750396720942599253801 := by
  unfold tailWord_2768849
  simp only [CollatzResearch.WordTrace]
  refine ⟨100988219545940429606269601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67325479697293619737513067 100988219545940429606269601)
  ·
    refine ⟨75741164659455322204702201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100988219545940429606269601 75741164659455322204702201)
    ·
      refine ⟨56805873494591491653526651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75741164659455322204702201 56805873494591491653526651)
      ·
        refine ⟨85208810241887237480289977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56805873494591491653526651 85208810241887237480289977)
        ·
          refine ⟨63906607681415428110217483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85208810241887237480289977 63906607681415428110217483)
          ·
            refine ⟨95859911522123142165326225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63906607681415428110217483 95859911522123142165326225)
            ·
              refine ⟨71894933641592356623994669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95859911522123142165326225 71894933641592356623994669)
              ·
                refine ⟨26960600115597133733998001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71894933641592356623994669 26960600115597133733998001)
                ·
                  refine ⟨20220450086697850300498501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26960600115597133733998001 20220450086697850300498501)
                  ·
                    refine ⟨3791334391255846931343469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20220450086697850300498501 3791334391255846931343469)
                    ·
                      refine ⟨1421750396720942599253801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3791334391255846931343469 1421750396720942599253801)
                      ·
                        rfl

theorem cell23_2768849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 4, 3].length) (baseStart_2768849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768849 prefixEnd_2768849 := by exact prefixLift 2768849
  have htrace : WordTrace (prefixWord ++ tailWord_2768849) baseStart_2768849 baseEnd_2768849 := by
    simpa [prefixWord, tailWord_2768849, baseEnd_2768849] using wordTrace_append hprefix tailTrace_2768849
  have hstable : (prefixWord ++ tailWord_2768849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768849).length < 2 ^ (prefixWord ++ tailWord_2768849).sum := by decide
  have hdescent : baseEnd_2768849 < baseStart_2768849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768863 : List Nat := [1, 1, 2, 3, 4, 1, 3, 1, 1, 4, 2]
def baseStart_2768863 : Nat := 118140960795 + 2768863 * 2 ^ 59
def prefixEnd_2768863 : Nat := 4983230072969 + 3 ^ 40 * 2768863 * 2
def baseEnd_2768863 : Nat := 1421757585450105544478737

theorem tailTrace_2768863 : CollatzResearch.WordTrace tailWord_2768863 prefixEnd_2768863 1421757585450105544478737 := by
  unfold tailWord_2768863
  simp only [CollatzResearch.WordTrace]
  refine ⟨100988730167889709997279243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67325820111926473331519495 100988730167889709997279243)
  ·
    refine ⟨151483095251834564995918865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100988730167889709997279243 151483095251834564995918865)
    ·
      refine ⟨113612321438875923746939149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151483095251834564995918865 113612321438875923746939149)
      ·
        refine ⟨42604620539578471405102181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113612321438875923746939149 42604620539578471405102181)
        ·
          refine ⟨7988366351170963388456659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42604620539578471405102181 7988366351170963388456659)
          ·
            refine ⟨11982549526756445082684989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7988366351170963388456659 11982549526756445082684989)
            ·
              refine ⟨4493456072533666906006871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11982549526756445082684989 4493456072533666906006871)
              ·
                refine ⟨6740184108800500359010307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4493456072533666906006871 6740184108800500359010307)
                ·
                  refine ⟨10110276163200750538515461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6740184108800500359010307 10110276163200750538515461)
                  ·
                    refine ⟨1895676780600140725971649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10110276163200750538515461 1895676780600140725971649)
                    ·
                      refine ⟨1421757585450105544478737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1895676780600140725971649 1421757585450105544478737)
                      ·
                        rfl

theorem cell23_2768863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 4, 2].length) (baseStart_2768863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768863 prefixEnd_2768863 := by exact prefixLift 2768863
  have htrace : WordTrace (prefixWord ++ tailWord_2768863) baseStart_2768863 baseEnd_2768863 := by
    simpa [prefixWord, tailWord_2768863, baseEnd_2768863] using wordTrace_append hprefix tailTrace_2768863
  have hstable : (prefixWord ++ tailWord_2768863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768863).length < 2 ^ (prefixWord ++ tailWord_2768863).sum := by decide
  have hdescent : baseEnd_2768863 < baseStart_2768863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768959 : List Nat := [1, 1, 2, 2, 3, 1, 2, 3, 8]
def baseStart_2768959 : Nat := 118140960795 + 2768959 * 2 ^ 59
def prefixEnd_2768959 : Nat := 4983230072969 + 3 ^ 40 * 2768959 * 2
def baseEnd_2768959 : Nat := 157978542176993018764255

theorem tailTrace_2768959 : CollatzResearch.WordTrace tailWord_2768959 prefixEnd_2768959 157978542176993018764255 := by
  unfold tailWord_2768959
  simp only [CollatzResearch.WordTrace]
  refine ⟨100992231575541918392773931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67328154383694612261849287 100992231575541918392773931)
  ·
    refine ⟨151488347363312877589160897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100992231575541918392773931 151488347363312877589160897)
    ·
      refine ⟨113616260522484658191870673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151488347363312877589160897 113616260522484658191870673)
      ·
        refine ⟨85212195391863493643903005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113616260522484658191870673 85212195391863493643903005)
        ·
          refine ⟨31954573271948810116463627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85212195391863493643903005 31954573271948810116463627)
          ·
            refine ⟨47931859907923215174695441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31954573271948810116463627 47931859907923215174695441)
            ·
              refine ⟨35948894930942411381021581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47931859907923215174695441 35948894930942411381021581)
              ·
                refine ⟨13480835599103404267883093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35948894930942411381021581 13480835599103404267883093)
                ·
                  refine ⟨157978542176993018764255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13480835599103404267883093 157978542176993018764255)
                  ·
                    rfl

theorem cell23_2768959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 8].length) (baseStart_2768959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768959 prefixEnd_2768959 := by exact prefixLift 2768959
  have htrace : WordTrace (prefixWord ++ tailWord_2768959) baseStart_2768959 baseEnd_2768959 := by
    simpa [prefixWord, tailWord_2768959, baseEnd_2768959] using wordTrace_append hprefix tailTrace_2768959
  have hstable : (prefixWord ++ tailWord_2768959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768959).length < 2 ^ (prefixWord ++ tailWord_2768959).sum := by decide
  have hdescent : baseEnd_2768959 < baseStart_2768959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768973 : List Nat := [1, 6, 1, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_2768973 : Nat := 118140960795 + 2768973 * 2 ^ 59
def prefixEnd_2768973 : Nat := 4983230072969 + 3 ^ 40 * 2768973 * 2
def baseEnd_2768973 : Nat := 1421814068322100114103231

theorem tailTrace_2768973 : CollatzResearch.WordTrace tailWord_2768973 prefixEnd_2768973 1421814068322100114103231 := by
  unfold tailWord_2768973
  simp only [CollatzResearch.WordTrace]
  refine ⟨100992742197491198783783573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67328494798327465855855715 100992742197491198783783573)
  ·
    refine ⟨4734034790507399942989855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 100992742197491198783783573 4734034790507399942989855)
    ·
      refine ⟨7101052185761099914484783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4734034790507399942989855 7101052185761099914484783)
      ·
        refine ⟨10651578278641649871727175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7101052185761099914484783 10651578278641649871727175)
        ·
          refine ⟨15977367417962474807590763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10651578278641649871727175 15977367417962474807590763)
          ·
            refine ⟨23966051126943712211386145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15977367417962474807590763 23966051126943712211386145)
            ·
              refine ⟨17974538345207784158539609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23966051126943712211386145 17974538345207784158539609)
              ·
                refine ⟨13480903758905838118904707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17974538345207784158539609 13480903758905838118904707)
                ·
                  refine ⟨20221355638358757178357061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13480903758905838118904707 20221355638358757178357061)
                  ·
                    refine ⟨3791504182192266970941949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20221355638358757178357061 3791504182192266970941949)
                    ·
                      refine ⟨1421814068322100114103231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3791504182192266970941949 1421814068322100114103231)
                      ·
                        rfl

theorem cell23_2768973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_2768973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2768973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2768973 prefixEnd_2768973 := by exact prefixLift 2768973
  have htrace : WordTrace (prefixWord ++ tailWord_2768973) baseStart_2768973 baseEnd_2768973 := by
    simpa [prefixWord, tailWord_2768973, baseEnd_2768973] using wordTrace_append hprefix tailTrace_2768973
  have hstable : (prefixWord ++ tailWord_2768973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768973).length < 2 ^ (prefixWord ++ tailWord_2768973).sum := by decide
  have hdescent : baseEnd_2768973 < baseStart_2768973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769019 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 2, 10]
def baseStart_2769019 : Nat := 118140960795 + 2769019 * 2 ^ 59
def prefixEnd_2769019 : Nat := 4983230072969 + 3 ^ 40 * 2769019 * 2
def baseEnd_2769019 : Nat := 473945896144068978042673

theorem tailTrace_2769019 : CollatzResearch.WordTrace tailWord_2769019 prefixEnd_2769019 473945896144068978042673 := by
  unfold tailWord_2769019
  simp only [CollatzResearch.WordTrace]
  refine ⟨100994419955324548639958111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67329613303549699093305407 100994419955324548639958111)
  ·
    refine ⟨151491629932986822959937167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100994419955324548639958111 151491629932986822959937167)
    ·
      refine ⟨227237444899480234439905751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151491629932986822959937167 227237444899480234439905751)
      ·
        refine ⟨340856167349220351659858627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227237444899480234439905751 340856167349220351659858627)
        ·
          refine ⟨511284251023830527489787941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340856167349220351659858627 511284251023830527489787941)
          ·
            refine ⟨95865797066968223904335239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 511284251023830527489787941 95865797066968223904335239)
            ·
              refine ⟨143798695600452335856502859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95865797066968223904335239 143798695600452335856502859)
              ·
                refine ⟨215698043400678503784754289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143798695600452335856502859 215698043400678503784754289)
                ·
                  refine ⟨161773532550508877838565717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215698043400678503784754289 161773532550508877838565717)
                  ·
                    refine ⟨473945896144068978042673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 161773532550508877838565717 473945896144068978042673)
                    ·
                      rfl

theorem cell23_2769019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 10].length) (baseStart_2769019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769019 prefixEnd_2769019 := by exact prefixLift 2769019
  have htrace : WordTrace (prefixWord ++ tailWord_2769019) baseStart_2769019 baseEnd_2769019 := by
    simpa [prefixWord, tailWord_2769019, baseEnd_2769019] using wordTrace_append hprefix tailTrace_2769019
  have hstable : (prefixWord ++ tailWord_2769019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769019).length < 2 ^ (prefixWord ++ tailWord_2769019).sum := by decide
  have hdescent : baseEnd_2769019 < baseStart_2769019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769020 : List Nat := [2, 2, 2, 1, 1, 5, 2, 1, 3, 1, 3]
def baseStart_2769020 : Nat := 118140960795 + 2769020 * 2 ^ 59
def prefixEnd_2769020 : Nat := 4983230072969 + 3 ^ 40 * 2769020 * 2
def baseEnd_2769020 : Nat := 1421838201912861430215515

theorem tailTrace_2769020 : CollatzResearch.WordTrace tailWord_2769020 prefixEnd_2769020 1421838201912861430215515 := by
  unfold tailWord_2769020
  simp only [CollatzResearch.WordTrace]
  refine ⟨50497228214160462905372257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67329637618880617207163009 50497228214160462905372257)
  ·
    refine ⟨37872921160620347179029193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50497228214160462905372257 37872921160620347179029193)
    ·
      refine ⟨28404690870465260384271895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37872921160620347179029193 28404690870465260384271895)
      ·
        refine ⟨42607036305697890576407843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28404690870465260384271895 42607036305697890576407843)
        ·
          refine ⟨63910554458546835864611765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42607036305697890576407843 63910554458546835864611765)
          ·
            refine ⟨5991614480488765862307353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63910554458546835864611765 5991614480488765862307353)
            ·
              refine ⟨4493710860366574396730515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5991614480488765862307353 4493710860366574396730515)
              ·
                refine ⟨6740566290549861595095773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4493710860366574396730515 6740566290549861595095773)
                ·
                  refine ⟨2527712358956198098160915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6740566290549861595095773 2527712358956198098160915)
                  ·
                    refine ⟨3791568538434297147241373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2527712358956198098160915 3791568538434297147241373)
                    ·
                      refine ⟨1421838201912861430215515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3791568538434297147241373 1421838201912861430215515)
                      ·
                        rfl

theorem cell23_2769020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_2769020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769020 prefixEnd_2769020 := by exact prefixLift 2769020
  have htrace : WordTrace (prefixWord ++ tailWord_2769020) baseStart_2769020 baseEnd_2769020 := by
    simpa [prefixWord, tailWord_2769020, baseEnd_2769020] using wordTrace_append hprefix tailTrace_2769020
  have hstable : (prefixWord ++ tailWord_2769020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769020).length < 2 ^ (prefixWord ++ tailWord_2769020).sum := by decide
  have hdescent : baseEnd_2769020 < baseStart_2769020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769053 : List Nat := [1, 4, 2, 1, 1, 3, 1, 2, 4, 4]
def baseStart_2769053 : Nat := 118140960795 + 2769053 * 2 ^ 59
def prefixEnd_2769053 : Nat := 4983230072969 + 3 ^ 40 * 2769053 * 2
def baseEnd_2769053 : Nat := 473951715591486600367621

theorem tailTrace_2769053 : CollatzResearch.WordTrace tailWord_2769053 prefixEnd_2769053 473951715591486600367621 := by
  unfold tailWord_2769053
  simp only [CollatzResearch.WordTrace]
  refine ⟨100995660037201372446695813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67330440024800914964463875 100995660037201372446695813)
  ·
    refine ⟨18936686256975257333755465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100995660037201372446695813 18936686256975257333755465)
    ·
      refine ⟨14202514692731443000316599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18936686256975257333755465 14202514692731443000316599)
      ·
        refine ⟨21303772039097164500474899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14202514692731443000316599 21303772039097164500474899)
        ·
          refine ⟨31955658058645746750712349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21303772039097164500474899 31955658058645746750712349)
          ·
            refine ⟨11983371771992155031517131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31955658058645746750712349 11983371771992155031517131)
            ·
              refine ⟨17975057657988232547275697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11983371771992155031517131 17975057657988232547275697)
              ·
                refine ⟨13481293243491174410456773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17975057657988232547275697 13481293243491174410456773)
                ·
                  refine ⟨2527742483154595201960645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13481293243491174410456773 2527742483154595201960645)
                  ·
                    refine ⟨473951715591486600367621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2527742483154595201960645 473951715591486600367621)
                    ·
                      rfl

theorem cell23_2769053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_2769053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769053 prefixEnd_2769053 := by exact prefixLift 2769053
  have htrace : WordTrace (prefixWord ++ tailWord_2769053) baseStart_2769053 baseEnd_2769053 := by
    simpa [prefixWord, tailWord_2769053, baseEnd_2769053] using wordTrace_append hprefix tailTrace_2769053
  have hstable : (prefixWord ++ tailWord_2769053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769053).length < 2 ^ (prefixWord ++ tailWord_2769053).sum := by decide
  have hdescent : baseEnd_2769053 < baseStart_2769053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769122 : List Nat := [3, 3, 4, 1, 2, 1, 2, 2, 1, 1, 3]
def baseStart_2769122 : Nat := 118140960795 + 2769122 * 2 ^ 59
def prefixEnd_2769122 : Nat := 4983230072969 + 3 ^ 40 * 2769122 * 2
def baseEnd_2769122 : Nat := 1421890576939620031140047

theorem tailTrace_2769122 : CollatzResearch.WordTrace tailWord_2769122 prefixEnd_2769122 1421890576939620031140047 := by
  unfold tailWord_2769122
  simp only [CollatzResearch.WordTrace]
  refine ⟨25249544168487849307739405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67332117782634264820638413 25249544168487849307739405)
  ·
    refine ⟨9468579063182943490402277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25249544168487849307739405 9468579063182943490402277)
    ·
      refine ⟨1775358574346801904450427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9468579063182943490402277 1775358574346801904450427)
      ·
        refine ⟨2663037861520202856675641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1775358574346801904450427 2663037861520202856675641)
        ·
          refine ⟨1997278396140152142506731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2663037861520202856675641 1997278396140152142506731)
          ·
            refine ⟨2995917594210228213760097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1997278396140152142506731 2995917594210228213760097)
            ·
              refine ⟨2246938195657671160320073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2995917594210228213760097 2246938195657671160320073)
              ·
                refine ⟨1685203646743253370240055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2246938195657671160320073 1685203646743253370240055)
                ·
                  refine ⟨2527805470114880055360083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1685203646743253370240055 2527805470114880055360083)
                  ·
                    refine ⟨3791708205172320083040125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2527805470114880055360083 3791708205172320083040125)
                    ·
                      refine ⟨1421890576939620031140047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3791708205172320083040125 1421890576939620031140047)
                      ·
                        rfl

theorem cell23_2769122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_2769122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769122 prefixEnd_2769122 := by exact prefixLift 2769122
  have htrace : WordTrace (prefixWord ++ tailWord_2769122) baseStart_2769122 baseEnd_2769122 := by
    simpa [prefixWord, tailWord_2769122, baseEnd_2769122] using wordTrace_append hprefix tailTrace_2769122
  have hstable : (prefixWord ++ tailWord_2769122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769122).length < 2 ^ (prefixWord ++ tailWord_2769122).sum := by decide
  have hdescent : baseEnd_2769122 < baseStart_2769122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769127 : List Nat := [1, 1, 5, 3, 1, 1, 1, 4, 2, 1, 3]
def baseStart_2769127 : Nat := 118140960795 + 2769127 * 2 ^ 59
def prefixEnd_2769127 : Nat := 4983230072969 + 3 ^ 40 * 2769127 * 2
def baseEnd_2769127 : Nat := 1421893144342892511577523

theorem tailTrace_2769127 : CollatzResearch.WordTrace tailWord_2769127 prefixEnd_2769127 1421893144342892511577523 := by
  unfold tailWord_2769127
  simp only [CollatzResearch.WordTrace]
  refine ⟨100998359038933283084889635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67332239359288855389926423 100998359038933283084889635)
  ·
    refine ⟨151497538558399924627334453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100998359038933283084889635 151497538558399924627334453)
    ·
      refine ⟨14202894239849992933812605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 151497538558399924627334453 14202894239849992933812605)
      ·
        refine ⟨5326085339943747350179727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14202894239849992933812605 5326085339943747350179727)
        ·
          refine ⟨7989128009915621025269591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5326085339943747350179727 7989128009915621025269591)
          ·
            refine ⟨11983692014873431537904387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7989128009915621025269591 11983692014873431537904387)
            ·
              refine ⟨17975538022310147306856581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11983692014873431537904387 17975538022310147306856581)
              ·
                refine ⟨3370413379183152620035609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17975538022310147306856581 3370413379183152620035609)
                ·
                  refine ⟨2527810034387364465026707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3370413379183152620035609 2527810034387364465026707)
                  ·
                    refine ⟨3791715051581046697540061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2527810034387364465026707 3791715051581046697540061)
                    ·
                      refine ⟨1421893144342892511577523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3791715051581046697540061 1421893144342892511577523)
                      ·
                        rfl

theorem cell23_2769127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_2769127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769127 prefixEnd_2769127 := by exact prefixLift 2769127
  have htrace : WordTrace (prefixWord ++ tailWord_2769127) baseStart_2769127 baseEnd_2769127 := by
    simpa [prefixWord, tailWord_2769127, baseEnd_2769127] using wordTrace_append hprefix tailTrace_2769127
  have hstable : (prefixWord ++ tailWord_2769127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769127).length < 2 ^ (prefixWord ++ tailWord_2769127).sum := by decide
  have hdescent : baseEnd_2769127 < baseStart_2769127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769136 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 5]
def baseStart_2769136 : Nat := 118140960795 + 2769136 * 2 ^ 59
def prefixEnd_2769136 : Nat := 4983230072969 + 3 ^ 40 * 2769136 * 2
def baseEnd_2769136 : Nat := 1421897765668782976364981

theorem tailTrace_2769136 : CollatzResearch.WordTrace tailWord_2769136 prefixEnd_2769136 1421897765668782976364981 := by
  unfold tailWord_2769136
  simp only [CollatzResearch.WordTrace]
  refine ⟨50499343647950338810983631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67332458197267118414644841 50499343647950338810983631)
  ·
    refine ⟨75749015471925508216475447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50499343647950338810983631 75749015471925508216475447)
    ·
      refine ⟨113623523207888262324713171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75749015471925508216475447 113623523207888262324713171)
      ·
        refine ⟨170435284811832393487069757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113623523207888262324713171 170435284811832393487069757)
        ·
          refine ⟨63913231804437147557651159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170435284811832393487069757 63913231804437147557651159)
          ·
            refine ⟨95869847706655721336476739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63913231804437147557651159 95869847706655721336476739)
            ·
              refine ⟨143804771559983582004715109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95869847706655721336476739 143804771559983582004715109)
              ·
                refine ⟨26963394667496921625884083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143804771559983582004715109 26963394667496921625884083)
                ·
                  refine ⟨40445092001245382438826125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26963394667496921625884083 40445092001245382438826125)
                  ·
                    refine ⟨15166909500467018414559797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40445092001245382438826125 15166909500467018414559797)
                    ·
                      refine ⟨1421897765668782976364981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15166909500467018414559797 1421897765668782976364981)
                      ·
                        rfl

theorem cell23_2769136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 5].length) (baseStart_2769136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769136 prefixEnd_2769136 := by exact prefixLift 2769136
  have htrace : WordTrace (prefixWord ++ tailWord_2769136) baseStart_2769136 baseEnd_2769136 := by
    simpa [prefixWord, tailWord_2769136, baseEnd_2769136] using wordTrace_append hprefix tailTrace_2769136
  have hstable : (prefixWord ++ tailWord_2769136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769136).length < 2 ^ (prefixWord ++ tailWord_2769136).sum := by decide
  have hdescent : baseEnd_2769136 < baseStart_2769136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769153 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 2, 4, 3]
def baseStart_2769153 : Nat := 118140960795 + 2769153 * 2 ^ 59
def prefixEnd_2769153 : Nat := 4983230072969 + 3 ^ 40 * 2769153 * 2
def baseEnd_2769153 : Nat := 1421906494839909409852403

theorem tailTrace_2769153 : CollatzResearch.WordTrace tailWord_2769153 prefixEnd_2769153 1421906494839909409852403 := by
  unfold tailWord_2769153
  simp only [CollatzResearch.WordTrace]
  refine ⟨100999307336839089525336113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67332871557892726350224075 100999307336839089525336113)
  ·
    refine ⟨75749480502629317144002085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100999307336839089525336113 75749480502629317144002085)
    ·
      refine ⟨14203027594242996964500391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75749480502629317144002085 14203027594242996964500391)
      ·
        refine ⟨21304541391364495446750587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14203027594242996964500391 21304541391364495446750587)
        ·
          refine ⟨31956812087046743170125881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21304541391364495446750587 31956812087046743170125881)
          ·
            refine ⟨23967609065285057377594411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31956812087046743170125881 23967609065285057377594411)
            ·
              refine ⟨35951413597927586066391617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23967609065285057377594411 35951413597927586066391617)
              ·
                refine ⟨26963560198445689549793713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35951413597927586066391617 26963560198445689549793713)
                ·
                  refine ⟨20222670148834267162345285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26963560198445689549793713 20222670148834267162345285)
                  ·
                    refine ⟨3791750652906425092939741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20222670148834267162345285 3791750652906425092939741)
                    ·
                      refine ⟨1421906494839909409852403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3791750652906425092939741 1421906494839909409852403)
                      ·
                        rfl

theorem cell23_2769153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_2769153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769153 prefixEnd_2769153 := by exact prefixLift 2769153
  have htrace : WordTrace (prefixWord ++ tailWord_2769153) baseStart_2769153 baseEnd_2769153 := by
    simpa [prefixWord, tailWord_2769153, baseEnd_2769153] using wordTrace_append hprefix tailTrace_2769153
  have hstable : (prefixWord ++ tailWord_2769153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769153).length < 2 ^ (prefixWord ++ tailWord_2769153).sum := by decide
  have hdescent : baseEnd_2769153 < baseStart_2769153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769184 : List Nat := [2, 1, 1, 5, 2, 1, 3, 2, 2, 2, 2]
def baseStart_2769184 : Nat := 118140960795 + 2769184 * 2 ^ 59
def prefixEnd_2769184 : Nat := 4983230072969 + 3 ^ 40 * 2769184 * 2
def baseEnd_2769184 : Nat := 1421922412740198788564761

theorem tailTrace_2769184 : CollatzResearch.WordTrace tailWord_2769184 prefixEnd_2769184 1421922412740198788564761 := by
  unfold tailWord_2769184
  simp only [CollatzResearch.WordTrace]
  refine ⟨50500218999863390909857303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67333625333151187879809737 50500218999863390909857303)
  ·
    refine ⟨75750328499795086364785955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50500218999863390909857303 75750328499795086364785955)
    ·
      refine ⟨113625492749692629547178933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75750328499795086364785955 113625492749692629547178933)
      ·
        refine ⟨10652389945283684020048025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113625492749692629547178933 10652389945283684020048025)
        ·
          refine ⟨7989292458962763015036019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10652389945283684020048025 7989292458962763015036019)
          ·
            refine ⟨11983938688444144522554029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7989292458962763015036019 11983938688444144522554029)
            ·
              refine ⟨4493977008166554195957761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11983938688444144522554029 4493977008166554195957761)
              ·
                refine ⟨3370482756124915646968321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4493977008166554195957761 3370482756124915646968321)
                ·
                  refine ⟨2527862067093686735226241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3370482756124915646968321 2527862067093686735226241)
                  ·
                    refine ⟨1895896550320265051419681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2527862067093686735226241 1895896550320265051419681)
                    ·
                      refine ⟨1421922412740198788564761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1895896550320265051419681 1421922412740198788564761)
                      ·
                        rfl

theorem cell23_2769184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_2769184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769184 prefixEnd_2769184 := by exact prefixLift 2769184
  have htrace : WordTrace (prefixWord ++ tailWord_2769184) baseStart_2769184 baseEnd_2769184 := by
    simpa [prefixWord, tailWord_2769184, baseEnd_2769184] using wordTrace_append hprefix tailTrace_2769184
  have hstable : (prefixWord ++ tailWord_2769184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769184).length < 2 ^ (prefixWord ++ tailWord_2769184).sum := by decide
  have hdescent : baseEnd_2769184 < baseStart_2769184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769201 : List Nat := [1, 2, 2, 3, 4, 1, 3, 1, 2, 2, 2]
def baseStart_2769201 : Nat := 118140960795 + 2769201 * 2 ^ 59
def prefixEnd_2769201 : Nat := 4983230072969 + 3 ^ 40 * 2769201 * 2
def baseEnd_2769201 : Nat := 1421931141911325222052183

theorem tailTrace_2769201 : CollatzResearch.WordTrace tailWord_2769201 prefixEnd_2769201 1421931141911325222052183 := by
  unfold tailWord_2769201
  simp only [CollatzResearch.WordTrace]
  refine ⟨101001058040665193723083457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67334038693776795815388971 101001058040665193723083457)
  ·
    refine ⟨75750793530498895292312593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101001058040665193723083457 75750793530498895292312593)
    ·
      refine ⟨56813095147874171469234445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75750793530498895292312593 56813095147874171469234445)
      ·
        refine ⟨21304910680452814300962917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56813095147874171469234445 21304910680452814300962917)
        ·
          refine ⟨3994670752584902681430547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21304910680452814300962917 3994670752584902681430547)
          ·
            refine ⟨5992006128877354022145821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3994670752584902681430547 5992006128877354022145821)
            ·
              refine ⟨2247002298329007758304683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5992006128877354022145821 2247002298329007758304683)
              ·
                refine ⟨3370503447493511637457025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2247002298329007758304683 3370503447493511637457025)
                ·
                  refine ⟨2527877585620133728092769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3370503447493511637457025 2527877585620133728092769)
                  ·
                    refine ⟨1895908189215100296069577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2527877585620133728092769 1895908189215100296069577)
                    ·
                      refine ⟨1421931141911325222052183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1895908189215100296069577 1421931141911325222052183)
                      ·
                        rfl

theorem cell23_2769201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_2769201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769201 prefixEnd_2769201 := by exact prefixLift 2769201
  have htrace : WordTrace (prefixWord ++ tailWord_2769201) baseStart_2769201 baseEnd_2769201 := by
    simpa [prefixWord, tailWord_2769201, baseEnd_2769201] using wordTrace_append hprefix tailTrace_2769201
  have hstable : (prefixWord ++ tailWord_2769201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769201).length < 2 ^ (prefixWord ++ tailWord_2769201).sum := by decide
  have hdescent : baseEnd_2769201 < baseStart_2769201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769223 : List Nat := [1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 4]
def baseStart_2769223 : Nat := 118140960795 + 2769223 * 2 ^ 59
def prefixEnd_2769223 : Nat := 4983230072969 + 3 ^ 40 * 2769223 * 2
def baseEnd_2769223 : Nat := 1421942438485724135977081

theorem tailTrace_2769223 : CollatzResearch.WordTrace tailWord_2769223 prefixEnd_2769223 1421942438485724135977081 := by
  unfold tailWord_2769223
  simp only [CollatzResearch.WordTrace]
  refine ⟨101001860446585491480384323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67334573631056994320256215 101001860446585491480384323)
  ·
    refine ⟨151502790669878237220576485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101001860446585491480384323 151502790669878237220576485)
    ·
      refine ⟨28406773250602169478858091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151502790669878237220576485 28406773250602169478858091)
      ·
        refine ⟨42610159875903254218287137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28406773250602169478858091 42610159875903254218287137)
        ·
          refine ⟨31957619906927440663715353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42610159875903254218287137 31957619906927440663715353)
          ·
            refine ⟨23968214930195580497786515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31957619906927440663715353 23968214930195580497786515)
            ·
              refine ⟨35952322395293370746679773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23968214930195580497786515 35952322395293370746679773)
              ·
                refine ⟨13482120898235014030004915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35952322395293370746679773 13482120898235014030004915)
                ·
                  refine ⟨20223181347352521045007373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13482120898235014030004915 20223181347352521045007373)
                  ·
                    refine ⟨7583693005257195391877765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20223181347352521045007373 7583693005257195391877765)
                    ·
                      refine ⟨1421942438485724135977081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7583693005257195391877765 1421942438485724135977081)
                      ·
                        rfl

theorem cell23_2769223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_2769223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769223 prefixEnd_2769223 := by exact prefixLift 2769223
  have htrace : WordTrace (prefixWord ++ tailWord_2769223) baseStart_2769223 baseEnd_2769223 := by
    simpa [prefixWord, tailWord_2769223, baseEnd_2769223] using wordTrace_append hprefix tailTrace_2769223
  have hstable : (prefixWord ++ tailWord_2769223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769223).length < 2 ^ (prefixWord ++ tailWord_2769223).sum := by decide
  have hdescent : baseEnd_2769223 < baseStart_2769223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769240 : List Nat := [2, 1, 2, 2, 1, 1, 2, 4, 2, 4, 2]
def baseStart_2769240 : Nat := 118140960795 + 2769240 * 2 ^ 59
def prefixEnd_2769240 : Nat := 4983230072969 + 3 ^ 40 * 2769240 * 2
def baseEnd_2769240 : Nat := 1421951167656850569464503

theorem tailTrace_2769240 : CollatzResearch.WordTrace tailWord_2769240 prefixEnd_2769240 1421951167656850569464503 := by
  unfold tailWord_2769240
  simp only [CollatzResearch.WordTrace]
  refine ⟨50501240243761951691876587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67334986991682602255835449 50501240243761951691876587)
  ·
    refine ⟨75751860365642927537814881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50501240243761951691876587 75751860365642927537814881)
    ·
      refine ⟨56813895274232195653361161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75751860365642927537814881 56813895274232195653361161)
      ·
        refine ⟨42610421455674146740020871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56813895274232195653361161 42610421455674146740020871)
        ·
          refine ⟨63915632183511220110031307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42610421455674146740020871 63915632183511220110031307)
          ·
            refine ⟨95873448275266830165046961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63915632183511220110031307 95873448275266830165046961)
            ·
              refine ⟨71905086206450122623785221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95873448275266830165046961 71905086206450122623785221)
              ·
                refine ⟨13482203663709397991959729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71905086206450122623785221 13482203663709397991959729)
                ·
                  refine ⟨10111652747782048493969797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13482203663709397991959729 10111652747782048493969797)
                  ·
                    refine ⟨1895934890209134092619337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10111652747782048493969797 1895934890209134092619337)
                    ·
                      refine ⟨1421951167656850569464503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1895934890209134092619337 1421951167656850569464503)
                      ·
                        rfl

theorem cell23_2769240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 2, 4, 2].length) (baseStart_2769240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769240 prefixEnd_2769240 := by exact prefixLift 2769240
  have htrace : WordTrace (prefixWord ++ tailWord_2769240) baseStart_2769240 baseEnd_2769240 := by
    simpa [prefixWord, tailWord_2769240, baseEnd_2769240] using wordTrace_append hprefix tailTrace_2769240
  have hstable : (prefixWord ++ tailWord_2769240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769240).length < 2 ^ (prefixWord ++ tailWord_2769240).sum := by decide
  have hdescent : baseEnd_2769240 < baseStart_2769240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769277 : List Nat := [1, 4, 1, 1, 2, 4, 2, 1, 2, 2, 3]
def baseStart_2769277 : Nat := 118140960795 + 2769277 * 2 ^ 59
def prefixEnd_2769277 : Nat := 4983230072969 + 3 ^ 40 * 2769277 * 2
def baseEnd_2769277 : Nat := 1421970166441066924701833

theorem tailTrace_2769277 : CollatzResearch.WordTrace tailWord_2769277 prefixEnd_2769277 1421970166441066924701833 := by
  unfold tailWord_2769277
  simp only [CollatzResearch.WordTrace]
  refine ⟨101003829988389858702850085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67335886658926572468566723 101003829988389858702850085)
  ·
    refine ⟨18938218122823098506784391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101003829988389858702850085 18938218122823098506784391)
    ·
      refine ⟨28407327184234647760176587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18938218122823098506784391 28407327184234647760176587)
      ·
        refine ⟨42610990776351971640264881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28407327184234647760176587 42610990776351971640264881)
        ·
          refine ⟨31958243082263978730198661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42610990776351971640264881 31958243082263978730198661)
          ·
            refine ⟨5992170577924496011912249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31958243082263978730198661 5992170577924496011912249)
            ·
              refine ⟨4494127933443372008934187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5992170577924496011912249 4494127933443372008934187)
              ·
                refine ⟨6741191900165058013401281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4494127933443372008934187 6741191900165058013401281)
                ·
                  refine ⟨5055893925123793510050961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6741191900165058013401281 5055893925123793510050961)
                  ·
                    refine ⟨3791920443842845132538221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5055893925123793510050961 3791920443842845132538221)
                    ·
                      refine ⟨1421970166441066924701833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3791920443842845132538221 1421970166441066924701833)
                      ·
                        rfl

theorem cell23_2769277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_2769277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769277 prefixEnd_2769277 := by exact prefixLift 2769277
  have htrace : WordTrace (prefixWord ++ tailWord_2769277) baseStart_2769277 baseEnd_2769277 := by
    simpa [prefixWord, tailWord_2769277, baseEnd_2769277] using wordTrace_append hprefix tailTrace_2769277
  have hstable : (prefixWord ++ tailWord_2769277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769277).length < 2 ^ (prefixWord ++ tailWord_2769277).sum := by decide
  have hdescent : baseEnd_2769277 < baseStart_2769277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769330 : List Nat := [3, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4]
def baseStart_2769330 : Nat := 118140960795 + 2769330 * 2 ^ 59
def prefixEnd_2769330 : Nat := 4983230072969 + 3 ^ 40 * 2769330 * 2
def baseEnd_2769330 : Nat := 1421997380915755217339089

theorem tailTrace_2769330 : CollatzResearch.WordTrace tailWord_2769330 prefixEnd_2769330 1421997380915755217339089 := by
  unfold tailWord_2769330
  simp only [CollatzResearch.WordTrace]
  refine ⟨25251440764299462188632361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67337175371465232503019629 25251440764299462188632361)
  ·
    refine ⟨18938580573224596641474271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25251440764299462188632361 18938580573224596641474271)
    ·
      refine ⟨28407870859836894962211407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18938580573224596641474271 28407870859836894962211407)
      ·
        refine ⟨42611806289755342443317111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28407870859836894962211407 42611806289755342443317111)
        ·
          refine ⟨63917709434633013664975667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42611806289755342443317111 63917709434633013664975667)
          ·
            refine ⟨95876564151949520497463501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63917709434633013664975667 95876564151949520497463501)
            ·
              refine ⟨35953711556981070186548813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95876564151949520497463501 35953711556981070186548813)
              ·
                refine ⟨13482641833867901319955805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35953711556981070186548813 13482641833867901319955805)
                ·
                  refine ⟨5055990687700462994983427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13482641833867901319955805 5055990687700462994983427)
                  ·
                    refine ⟨7583986031550694492475141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5055990687700462994983427 7583986031550694492475141)
                    ·
                      refine ⟨1421997380915755217339089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7583986031550694492475141 1421997380915755217339089)
                      ·
                        rfl

theorem cell23_2769330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_2769330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769330 prefixEnd_2769330 := by exact prefixLift 2769330
  have htrace : WordTrace (prefixWord ++ tailWord_2769330) baseStart_2769330 baseEnd_2769330 := by
    simpa [prefixWord, tailWord_2769330, baseEnd_2769330] using wordTrace_append hprefix tailTrace_2769330
  have hstable : (prefixWord ++ tailWord_2769330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769330).length < 2 ^ (prefixWord ++ tailWord_2769330).sum := by decide
  have hdescent : baseEnd_2769330 < baseStart_2769330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769341 : List Nat := [1, 4, 1, 2, 2, 3, 2, 3, 1, 1, 3]
def baseStart_2769341 : Nat := 118140960795 + 2769341 * 2 ^ 59
def prefixEnd_2769341 : Nat := 4983230072969 + 3 ^ 40 * 2769341 * 2
def baseEnd_2769341 : Nat := 1422003029202954674301539

theorem tailTrace_2769341 : CollatzResearch.WordTrace tailWord_2769341 prefixEnd_2769341 1422003029202954674301539 := by
  unfold tailWord_2769341
  simp only [CollatzResearch.WordTrace]
  refine ⟨101006164260157997633179877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67337442840105331755453251 101006164260157997633179877)
  ·
    refine ⟨18938655798779624556221227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101006164260157997633179877 18938655798779624556221227)
    ·
      refine ⟨28407983698169436834331841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18938655798779624556221227 28407983698169436834331841)
      ·
        refine ⟨21305987773627077625748881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28407983698169436834331841 21305987773627077625748881)
        ·
          refine ⟨15979490830220308219311661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21305987773627077625748881 15979490830220308219311661)
          ·
            refine ⟨5992309061332615582241873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15979490830220308219311661 5992309061332615582241873)
            ·
              refine ⟨4494231795999461686681405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5992309061332615582241873 4494231795999461686681405)
              ·
                refine ⟨1685336923499798132505527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4494231795999461686681405 1685336923499798132505527)
                ·
                  refine ⟨2528005385249697198758291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1685336923499798132505527 2528005385249697198758291)
                  ·
                    refine ⟨3792008077874545798137437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2528005385249697198758291 3792008077874545798137437)
                    ·
                      refine ⟨1422003029202954674301539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3792008077874545798137437 1422003029202954674301539)
                      ·
                        rfl

theorem cell23_2769341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_2769341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769341 prefixEnd_2769341 := by exact prefixLift 2769341
  have htrace : WordTrace (prefixWord ++ tailWord_2769341) baseStart_2769341 baseEnd_2769341 := by
    simpa [prefixWord, tailWord_2769341, baseEnd_2769341] using wordTrace_append hprefix tailTrace_2769341
  have hstable : (prefixWord ++ tailWord_2769341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769341).length < 2 ^ (prefixWord ++ tailWord_2769341).sum := by decide
  have hdescent : baseEnd_2769341 < baseStart_2769341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769343 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 6]
def baseStart_2769343 : Nat := 118140960795 + 2769343 * 2 ^ 59
def prefixEnd_2769343 : Nat := 4983230072969 + 3 ^ 40 * 2769343 * 2
def baseEnd_2769343 : Nat := 1422004056164263666476529

theorem tailTrace_2769343 : CollatzResearch.WordTrace tailWord_2769343 prefixEnd_2769343 1422004056164263666476529 := by
  unfold tailWord_2769343
  simp only [CollatzResearch.WordTrace]
  refine ⟨101006237206150751974752683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67337491470767167983168455 101006237206150751974752683)
  ·
    refine ⟨151509355809226127962129025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101006237206150751974752683 151509355809226127962129025)
    ·
      refine ⟨113632016856919595971596769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151509355809226127962129025 113632016856919595971596769)
      ·
        refine ⟨85224012642689696978697577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113632016856919595971596769 85224012642689696978697577)
        ·
          refine ⟨63918009482017272734023183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85224012642689696978697577 63918009482017272734023183)
          ·
            refine ⟨95877014223025909101034775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63918009482017272734023183 95877014223025909101034775)
            ·
              refine ⟨143815521334538863651552163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95877014223025909101034775 143815521334538863651552163)
              ·
                refine ⟨215723282001808295477328245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143815521334538863651552163 215723282001808295477328245)
                ·
                  refine ⟨20224057687669527700999523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 215723282001808295477328245 20224057687669527700999523)
                  ·
                    refine ⟨30336086531504291551499285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20224057687669527700999523 30336086531504291551499285)
                    ·
                      refine ⟨1422004056164263666476529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30336086531504291551499285 1422004056164263666476529)
                      ·
                        rfl

theorem cell23_2769343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_2769343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769343 prefixEnd_2769343 := by exact prefixLift 2769343
  have htrace : WordTrace (prefixWord ++ tailWord_2769343) baseStart_2769343 baseEnd_2769343 := by
    simpa [prefixWord, tailWord_2769343, baseEnd_2769343] using wordTrace_append hprefix tailTrace_2769343
  have hstable : (prefixWord ++ tailWord_2769343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769343).length < 2 ^ (prefixWord ++ tailWord_2769343).sum := by decide
  have hdescent : baseEnd_2769343 < baseStart_2769343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769347 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 7, 2, 2]
def baseStart_2769347 : Nat := 118140960795 + 2769347 * 2 ^ 59
def prefixEnd_2769347 : Nat := 4983230072969 + 3 ^ 40 * 2769347 * 2
def baseEnd_2769347 : Nat := 1422006110086881650826511

theorem tailTrace_2769347 : CollatzResearch.WordTrace tailWord_2769347 prefixEnd_2769347 1422006110086881650826511 := by
  unfold tailWord_2769347
  simp only [CollatzResearch.WordTrace]
  refine ⟨101006383098136260657898295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67337588732090840438598863 101006383098136260657898295)
  ·
    refine ⟨151509574647204390986847443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101006383098136260657898295 151509574647204390986847443)
    ·
      refine ⟨227264361970806586480271165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151509574647204390986847443 227264361970806586480271165)
      ·
        refine ⟨85224135739052469930101687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227264361970806586480271165 85224135739052469930101687)
        ·
          refine ⟨127836203608578704895152531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85224135739052469930101687 127836203608578704895152531)
          ·
            refine ⟨191754305412868057342728797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127836203608578704895152531 191754305412868057342728797)
            ·
              refine ⟨71907864529825521503523299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191754305412868057342728797 71907864529825521503523299)
              ·
                refine ⟨107861796794738282255284949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71907864529825521503523299 107861796794738282255284949)
                ·
                  refine ⟨2528010862376678490358241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 107861796794738282255284949 2528010862376678490358241)
                  ·
                    refine ⟨1896008146782508867768681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2528010862376678490358241 1896008146782508867768681)
                    ·
                      refine ⟨1422006110086881650826511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1896008146782508867768681 1422006110086881650826511)
                      ·
                        rfl

theorem cell23_2769347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7, 2, 2].length) (baseStart_2769347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769347 prefixEnd_2769347 := by exact prefixLift 2769347
  have htrace : WordTrace (prefixWord ++ tailWord_2769347) baseStart_2769347 baseEnd_2769347 := by
    simpa [prefixWord, tailWord_2769347, baseEnd_2769347] using wordTrace_append hprefix tailTrace_2769347
  have hstable : (prefixWord ++ tailWord_2769347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769347).length < 2 ^ (prefixWord ++ tailWord_2769347).sum := by decide
  have hdescent : baseEnd_2769347 < baseStart_2769347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769384 : List Nat := [2, 1, 4, 1, 1, 4, 2, 2, 1, 2, 3]
def baseStart_2769384 : Nat := 118140960795 + 2769384 * 2 ^ 59
def prefixEnd_2769384 : Nat := 4983230072969 + 3 ^ 40 * 2769384 * 2
def baseEnd_2769384 : Nat := 1422025108871098006063841

theorem tailTrace_2769384 : CollatzResearch.WordTrace tailWord_2769384 prefixEnd_2769384 1422025108871098006063841 := by
  unfold tailWord_2769384
  simp only [CollatzResearch.WordTrace]
  refine ⟨50503866299501107988497603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67338488399334810651330137 50503866299501107988497603)
  ·
    refine ⟨75755799449251661982746405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50503866299501107988497603 75755799449251661982746405)
    ·
      refine ⟨14204212396734686621764951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75755799449251661982746405 14204212396734686621764951)
      ·
        refine ⟨21306318595102029932647427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14204212396734686621764951 21306318595102029932647427)
        ·
          refine ⟨31959477892653044898971141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21306318595102029932647427 31959477892653044898971141)
          ·
            refine ⟨5992402104872445918557089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31959477892653044898971141 5992402104872445918557089)
            ·
              refine ⟨4494301578654334438917817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5992402104872445918557089 4494301578654334438917817)
              ·
                refine ⟨3370726183990750829188363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4494301578654334438917817 3370726183990750829188363)
                ·
                  refine ⟨5056089275986126243782545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3370726183990750829188363 5056089275986126243782545)
                  ·
                    refine ⟨3792066956989594682836909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5056089275986126243782545 3792066956989594682836909)
                    ·
                      refine ⟨1422025108871098006063841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3792066956989594682836909 1422025108871098006063841)
                      ·
                        rfl

theorem cell23_2769384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_2769384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769384 prefixEnd_2769384 := by exact prefixLift 2769384
  have htrace : WordTrace (prefixWord ++ tailWord_2769384) baseStart_2769384 baseEnd_2769384 := by
    simpa [prefixWord, tailWord_2769384, baseEnd_2769384] using wordTrace_append hprefix tailTrace_2769384
  have hstable : (prefixWord ++ tailWord_2769384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769384).length < 2 ^ (prefixWord ++ tailWord_2769384).sum := by decide
  have hdescent : baseEnd_2769384 < baseStart_2769384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769415 : List Nat := [1, 1, 4, 3, 3, 1, 3, 2, 1, 2, 2]
def baseStart_2769415 : Nat := 118140960795 + 2769415 * 2 ^ 59
def prefixEnd_2769415 : Nat := 4983230072969 + 3 ^ 40 * 2769415 * 2
def baseEnd_2769415 : Nat := 1422041026771387384776199

theorem tailTrace_2769415 : CollatzResearch.WordTrace tailWord_2769415 prefixEnd_2769415 1422041026771387384776199 := by
  unfold tailWord_2769415
  simp only [CollatzResearch.WordTrace]
  refine ⟨101008863261889908271373699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67339242174593272180915799 101008863261889908271373699)
  ·
    refine ⟨151513294892834862407060549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101008863261889908271373699 151513294892834862407060549)
    ·
      refine ⟨28408742792406536701323853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151513294892834862407060549 28408742792406536701323853)
      ·
        refine ⟨10653278547152451262996445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28408742792406536701323853 10653278547152451262996445)
        ·
          refine ⟨3994979455182169223623667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10653278547152451262996445 3994979455182169223623667)
          ·
            refine ⟨5992469182773253835435501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3994979455182169223623667 5992469182773253835435501)
            ·
              refine ⟨2247175943539970188288313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5992469182773253835435501 2247175943539970188288313)
              ·
                refine ⟨1685381957654977641216235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2247175943539970188288313 1685381957654977641216235)
                ·
                  refine ⟨2528072936482466461824353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1685381957654977641216235 2528072936482466461824353)
                  ·
                    refine ⟨1896054702361849846368265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2528072936482466461824353 1896054702361849846368265)
                    ·
                      refine ⟨1422041026771387384776199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1896054702361849846368265 1422041026771387384776199)
                      ·
                        rfl

theorem cell23_2769415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_2769415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769415 prefixEnd_2769415 := by exact prefixLift 2769415
  have htrace : WordTrace (prefixWord ++ tailWord_2769415) baseStart_2769415 baseEnd_2769415 := by
    simpa [prefixWord, tailWord_2769415, baseEnd_2769415] using wordTrace_append hprefix tailTrace_2769415
  have hstable : (prefixWord ++ tailWord_2769415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769415).length < 2 ^ (prefixWord ++ tailWord_2769415).sum := by decide
  have hdescent : baseEnd_2769415 < baseStart_2769415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769471 : List Nat := [1, 1, 2, 2, 3, 2, 4, 2, 2, 2, 2]
def baseStart_2769471 : Nat := 118140960795 + 2769471 * 2 ^ 59
def prefixEnd_2769471 : Nat := 4983230072969 + 3 ^ 40 * 2769471 * 2
def baseEnd_2769471 : Nat := 1422069781688039165675941

theorem tailTrace_2769471 : CollatzResearch.WordTrace tailWord_2769471 prefixEnd_2769471 1422069781688039165675941 := by
  unfold tailWord_2769471
  simp only [CollatzResearch.WordTrace]
  refine ⟨101010905749687029835412267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67340603833124686556941511 101010905749687029835412267)
  ·
    refine ⟨151516358624530544753118401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101010905749687029835412267 151516358624530544753118401)
    ·
      refine ⟨113637268968397908564838801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151516358624530544753118401 113637268968397908564838801)
      ·
        refine ⟨85227951726298431423629101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113637268968397908564838801 85227951726298431423629101)
        ·
          refine ⟨31960481897361911783860913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85227951726298431423629101 31960481897361911783860913)
          ·
            refine ⟨23970361423021433837895685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31960481897361911783860913 23970361423021433837895685)
            ·
              refine ⟨4494442766816518844605441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23970361423021433837895685 4494442766816518844605441)
              ·
                refine ⟨3370832075112389133454081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4494442766816518844605441 3370832075112389133454081)
                ·
                  refine ⟨2528124056334291850090561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3370832075112389133454081 2528124056334291850090561)
                  ·
                    refine ⟨1896093042250718887567921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2528124056334291850090561 1896093042250718887567921)
                    ·
                      refine ⟨1422069781688039165675941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1896093042250718887567921 1422069781688039165675941)
                      ·
                        rfl

theorem cell23_2769471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2, 2, 2].length) (baseStart_2769471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769471 prefixEnd_2769471 := by exact prefixLift 2769471
  have htrace : WordTrace (prefixWord ++ tailWord_2769471) baseStart_2769471 baseEnd_2769471 := by
    simpa [prefixWord, tailWord_2769471, baseEnd_2769471] using wordTrace_append hprefix tailTrace_2769471
  have hstable : (prefixWord ++ tailWord_2769471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769471).length < 2 ^ (prefixWord ++ tailWord_2769471).sum := by decide
  have hdescent : baseEnd_2769471 < baseStart_2769471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769527 : List Nat := [1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 4]
def baseStart_2769527 : Nat := 118140960795 + 2769527 * 2 ^ 59
def prefixEnd_2769527 : Nat := 4983230072969 + 3 ^ 40 * 2769527 * 2
def baseEnd_2769527 : Nat := 1422098536604690946575683

theorem tailTrace_2769527 : CollatzResearch.WordTrace tailWord_2769527 prefixEnd_2769527 1422098536604690946575683 := by
  unfold tailWord_2769527
  simp only [CollatzResearch.WordTrace]
  refine ⟨101012948237484151399450835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67341965491656100932967223 101012948237484151399450835)
  ·
    refine ⟨151519422356226227099176253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101012948237484151399450835 151519422356226227099176253)
    ·
      refine ⟨56819783383584835162191095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151519422356226227099176253 56819783383584835162191095)
      ·
        refine ⟨85229675075377252743286643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56819783383584835162191095 85229675075377252743286643)
        ·
          refine ⟨127844512613065879114929965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85229675075377252743286643 127844512613065879114929965)
          ·
            refine ⟨47941692229899704668098737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127844512613065879114929965 47941692229899704668098737)
            ·
              refine ⟨35956269172424778501074053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47941692229899704668098737 35956269172424778501074053)
              ·
                refine ⟨6741800469829645968951385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35956269172424778501074053 6741800469829645968951385)
                ·
                  refine ⟨5056350352372234476713539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6741800469829645968951385 5056350352372234476713539)
                  ·
                    refine ⟨7584525528558351715070309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5056350352372234476713539 7584525528558351715070309)
                    ·
                      refine ⟨1422098536604690946575683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7584525528558351715070309 1422098536604690946575683)
                      ·
                        rfl

theorem cell23_2769527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_2769527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769527 prefixEnd_2769527 := by exact prefixLift 2769527
  have htrace : WordTrace (prefixWord ++ tailWord_2769527) baseStart_2769527 baseEnd_2769527 := by
    simpa [prefixWord, tailWord_2769527, baseEnd_2769527] using wordTrace_append hprefix tailTrace_2769527
  have hstable : (prefixWord ++ tailWord_2769527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769527).length < 2 ^ (prefixWord ++ tailWord_2769527).sum := by decide
  have hdescent : baseEnd_2769527 < baseStart_2769527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769547 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 6, 2, 3]
def baseStart_2769547 : Nat := 118140960795 + 2769547 * 2 ^ 59
def prefixEnd_2769547 : Nat := 4983230072969 + 3 ^ 40 * 2769547 * 2
def baseEnd_2769547 : Nat := 1422108806217780868325591

theorem tailTrace_2769547 : CollatzResearch.WordTrace tailWord_2769547 prefixEnd_2769547 1422108806217780868325591 := by
  unfold tailWord_2769547
  simp only [CollatzResearch.WordTrace]
  refine ⟨101013677697411694815178895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67342451798274463210119263 101013677697411694815178895)
  ·
    refine ⟨151520516546117542222768343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101013677697411694815178895 151520516546117542222768343)
    ·
      refine ⟨227280774819176313334152515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151520516546117542222768343 227280774819176313334152515)
      ·
        refine ⟨340921162228764470001228773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227280774819176313334152515 340921162228764470001228773)
        ·
          refine ⟨63922717917893338125230395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 340921162228764470001228773 63922717917893338125230395)
          ·
            refine ⟨95884076876840007187845593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63922717917893338125230395 95884076876840007187845593)
            ·
              refine ⟨71913057657630005390884195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95884076876840007187845593 71913057657630005390884195)
              ·
                refine ⟨107869586486445008086326293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71913057657630005390884195 107869586486445008086326293)
                ·
                  refine ⟨5056386866552109754046545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107869586486445008086326293 5056386866552109754046545)
                  ·
                    refine ⟨3792290149914082315534909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5056386866552109754046545 3792290149914082315534909)
                    ·
                      refine ⟨1422108806217780868325591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3792290149914082315534909 1422108806217780868325591)
                      ·
                        rfl

theorem cell23_2769547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2, 3].length) (baseStart_2769547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769547 prefixEnd_2769547 := by exact prefixLift 2769547
  have htrace : WordTrace (prefixWord ++ tailWord_2769547) baseStart_2769547 baseEnd_2769547 := by
    simpa [prefixWord, tailWord_2769547, baseEnd_2769547] using wordTrace_append hprefix tailTrace_2769547
  have hstable : (prefixWord ++ tailWord_2769547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769547).length < 2 ^ (prefixWord ++ tailWord_2769547).sum := by decide
  have hdescent : baseEnd_2769547 < baseStart_2769547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769564 : List Nat := [2, 2, 3, 2, 2, 1, 2, 1, 1, 4, 3]
def baseStart_2769564 : Nat := 118140960795 + 2769564 * 2 ^ 59
def prefixEnd_2769564 : Nat := 4983230072969 + 3 ^ 40 * 2769564 * 2
def baseEnd_2769564 : Nat := 1422117535388907301813013

theorem tailTrace_2769564 : CollatzResearch.WordTrace tailWord_2769564 prefixEnd_2769564 1422117535388907301813013 := by
  unfold tailWord_2769564
  simp only [CollatzResearch.WordTrace]
  refine ⟨50507148869175053359273873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67342865158900071145698497 50507148869175053359273873)
  ·
    refine ⟨37880361651881290019455405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50507148869175053359273873 37880361651881290019455405)
    ·
      refine ⟨14205135619455483757295777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37880361651881290019455405 14205135619455483757295777)
      ·
        refine ⟨10653851714591612817971833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14205135619455483757295777 10653851714591612817971833)
        ·
          refine ⟨7990388785943709613478875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10653851714591612817971833 7990388785943709613478875)
          ·
            refine ⟨11985583178915564420218313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7990388785943709613478875 11985583178915564420218313)
            ·
              refine ⟨8989187384186673315163735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11985583178915564420218313 8989187384186673315163735)
              ·
                refine ⟨13483781076280009972745603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8989187384186673315163735 13483781076280009972745603)
                ·
                  refine ⟨20225671614420014959118405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13483781076280009972745603 20225671614420014959118405)
                  ·
                    refine ⟨3792313427703752804834701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20225671614420014959118405 3792313427703752804834701)
                    ·
                      refine ⟨1422117535388907301813013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3792313427703752804834701 1422117535388907301813013)
                      ·
                        rfl

theorem cell23_2769564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_2769564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769564 prefixEnd_2769564 := by exact prefixLift 2769564
  have htrace : WordTrace (prefixWord ++ tailWord_2769564) baseStart_2769564 baseEnd_2769564 := by
    simpa [prefixWord, tailWord_2769564, baseEnd_2769564] using wordTrace_append hprefix tailTrace_2769564
  have hstable : (prefixWord ++ tailWord_2769564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769564).length < 2 ^ (prefixWord ++ tailWord_2769564).sum := by decide
  have hdescent : baseEnd_2769564 < baseStart_2769564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769578 : List Nat := [3, 1, 5, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_2769578 : Nat := 118140960795 + 2769578 * 2 ^ 59
def prefixEnd_2769578 : Nat := 4983230072969 + 3 ^ 40 * 2769578 * 2
def baseEnd_2769578 : Nat := 1422124724118070247037949

theorem tailTrace_2769578 : CollatzResearch.WordTrace tailWord_2769578 prefixEnd_2769578 1422124724118070247037949 := by
  unfold tailWord_2769578
  simp only [CollatzResearch.WordTrace]
  refine ⟨25253702090074846777389347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67343205573532924739704925 25253702090074846777389347)
  ·
    refine ⟨37880553135112270166084021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25253702090074846777389347 37880553135112270166084021)
    ·
      refine ⟨3551301856416775328070377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37880553135112270166084021 3551301856416775328070377)
      ·
        refine ⟨2663476392312581496052783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3551301856416775328070377 2663476392312581496052783)
        ·
          refine ⟨3995214588468872244079175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2663476392312581496052783 3995214588468872244079175)
          ·
            refine ⟨5992821882703308366118763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3995214588468872244079175 5992821882703308366118763)
            ·
              refine ⟨8989232824054962549178145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5992821882703308366118763 8989232824054962549178145)
              ·
                refine ⟨6741924618041221911883609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8989232824054962549178145 6741924618041221911883609)
                ·
                  refine ⟨5056443463530916433912707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6741924618041221911883609 5056443463530916433912707)
                  ·
                    refine ⟨7584665195296374650869061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5056443463530916433912707 7584665195296374650869061)
                    ·
                      refine ⟨1422124724118070247037949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7584665195296374650869061 1422124724118070247037949)
                      ·
                        rfl

theorem cell23_2769578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_2769578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769578 prefixEnd_2769578 := by exact prefixLift 2769578
  have htrace : WordTrace (prefixWord ++ tailWord_2769578) baseStart_2769578 baseEnd_2769578 := by
    simpa [prefixWord, tailWord_2769578, baseEnd_2769578] using wordTrace_append hprefix tailTrace_2769578
  have hstable : (prefixWord ++ tailWord_2769578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769578).length < 2 ^ (prefixWord ++ tailWord_2769578).sum := by decide
  have hdescent : baseEnd_2769578 < baseStart_2769578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769581 : List Nat := [1, 5, 2, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_2769581 : Nat := 118140960795 + 2769581 * 2 ^ 59
def prefixEnd_2769581 : Nat := 4983230072969 + 3 ^ 40 * 2769581 * 2
def baseEnd_2769581 : Nat := 1422126264560033735300435

theorem tailTrace_2769581 : CollatzResearch.WordTrace tailWord_2769581 prefixEnd_2769581 1422126264560033735300435 := by
  unfold tailWord_2769581
  simp only [CollatzResearch.WordTrace]
  refine ⟨101014917779288518621916597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67343278519525679081277731 101014917779288518621916597)
  ·
    refine ⟨9470148541808298620804681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101014917779288518621916597 9470148541808298620804681)
    ·
      refine ⟨7102611406356223965603511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9470148541808298620804681 7102611406356223965603511)
      ·
        refine ⟨10653917109534335948405267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7102611406356223965603511 10653917109534335948405267)
        ·
          refine ⟨15980875664301503922607901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10653917109534335948405267 15980875664301503922607901)
          ·
            refine ⟨5992828374113063970977963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15980875664301503922607901 5992828374113063970977963)
            ·
              refine ⟨8989242561169595956466945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5992828374113063970977963 8989242561169595956466945)
              ·
                refine ⟨6741931920877196967350209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8989242561169595956466945 6741931920877196967350209)
                ·
                  refine ⟨5056448940657897725512657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6741931920877196967350209 5056448940657897725512657)
                  ·
                    refine ⟨3792336705493423294134493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5056448940657897725512657 3792336705493423294134493)
                    ·
                      refine ⟨1422126264560033735300435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3792336705493423294134493 1422126264560033735300435)
                      ·
                        rfl

theorem cell23_2769581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_2769581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769581 prefixEnd_2769581 := by exact prefixLift 2769581
  have htrace : WordTrace (prefixWord ++ tailWord_2769581) baseStart_2769581 baseEnd_2769581 := by
    simpa [prefixWord, tailWord_2769581, baseEnd_2769581] using wordTrace_append hprefix tailTrace_2769581
  have hstable : (prefixWord ++ tailWord_2769581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769581).length < 2 ^ (prefixWord ++ tailWord_2769581).sum := by decide
  have hdescent : baseEnd_2769581 < baseStart_2769581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769614 : List Nat := [4, 1, 1, 1, 3, 3, 1, 1, 3, 5]
def baseStart_2769614 : Nat := 118140960795 + 2769614 * 2 ^ 59
def prefixEnd_2769614 : Nat := 4983230072969 + 3 ^ 40 * 2769614 * 2
def baseEnd_2769614 : Nat := 474047736473877368729261

theorem tailTrace_2769614 : CollatzResearch.WordTrace tailWord_2769614 prefixEnd_2769614 474047736473877368729261 := by
  unfold tailWord_2769614
  simp only [CollatzResearch.WordTrace]
  refine ⟨12627015173521120657233487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67344080925445976838578597 12627015173521120657233487)
  ·
    refine ⟨18940522760281680985850231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12627015173521120657233487 18940522760281680985850231)
    ·
      refine ⟨28410784140422521478775347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18940522760281680985850231 28410784140422521478775347)
      ·
        refine ⟨42616176210633782218163021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28410784140422521478775347 42616176210633782218163021)
        ·
          refine ⟨15981066078987668331811133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42616176210633782218163021 15981066078987668331811133)
          ·
            refine ⟨5992899779620375624429175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15981066078987668331811133 5992899779620375624429175)
            ·
              refine ⟨8989349669430563436643763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5992899779620375624429175 8989349669430563436643763)
              ·
                refine ⟨13484024504145845154965645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8989349669430563436643763 13484024504145845154965645)
                ·
                  refine ⟨5056509189054691933112117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13484024504145845154965645 5056509189054691933112117)
                  ·
                    refine ⟨474047736473877368729261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5056509189054691933112117 474047736473877368729261)
                    ·
                      rfl

theorem cell23_2769614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_2769614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769614 prefixEnd_2769614 := by exact prefixLift 2769614
  have htrace : WordTrace (prefixWord ++ tailWord_2769614) baseStart_2769614 baseEnd_2769614 := by
    simpa [prefixWord, tailWord_2769614, baseEnd_2769614] using wordTrace_append hprefix tailTrace_2769614
  have hstable : (prefixWord ++ tailWord_2769614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769614).length < 2 ^ (prefixWord ++ tailWord_2769614).sum := by decide
  have hdescent : baseEnd_2769614 < baseStart_2769614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769631 : List Nat := [1, 1, 2, 3, 2, 4, 3, 1, 1, 5]
def baseStart_2769631 : Nat := 118140960795 + 2769631 * 2 ^ 59
def prefixEnd_2769631 : Nat := 4983230072969 + 3 ^ 40 * 2769631 * 2
def baseEnd_2769631 : Nat := 474050646197586179891735

theorem tailTrace_2769631 : CollatzResearch.WordTrace tailWord_2769631 prefixEnd_2769631 474050646197586179891735 := by
  unfold tailWord_2769631
  simp only [CollatzResearch.WordTrace]
  refine ⟨101016741429107377161236747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67344494286071584774157831 101016741429107377161236747)
  ·
    refine ⟨151525112143661065741855121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101016741429107377161236747 151525112143661065741855121)
    ·
      refine ⟨113643834107745799306391341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151525112143661065741855121 113643834107745799306391341)
      ·
        refine ⟨42616437790404674739896753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113643834107745799306391341 42616437790404674739896753)
        ·
          refine ⟨31962328342803506054922565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42616437790404674739896753 31962328342803506054922565)
          ·
            refine ⟨5992936564275657385297981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31962328342803506054922565 5992936564275657385297981)
            ·
              refine ⟨2247351211603371519486743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5992936564275657385297981 2247351211603371519486743)
              ·
                refine ⟨3371026817405057279230115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2247351211603371519486743 3371026817405057279230115)
                ·
                  refine ⟨5056540226107585918845173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3371026817405057279230115 5056540226107585918845173)
                  ·
                    refine ⟨474050646197586179891735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5056540226107585918845173 474050646197586179891735)
                    ·
                      rfl

theorem cell23_2769631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 1, 5].length) (baseStart_2769631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769631 prefixEnd_2769631 := by exact prefixLift 2769631
  have htrace : WordTrace (prefixWord ++ tailWord_2769631) baseStart_2769631 baseEnd_2769631 := by
    simpa [prefixWord, tailWord_2769631, baseEnd_2769631] using wordTrace_append hprefix tailTrace_2769631
  have hstable : (prefixWord ++ tailWord_2769631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769631).length < 2 ^ (prefixWord ++ tailWord_2769631).sum := by decide
  have hdescent : baseEnd_2769631 < baseStart_2769631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769651 : List Nat := [1, 1, 1, 2, 2, 3, 1, 5, 3, 2, 2]
def baseStart_2769651 : Nat := 118140960795 + 2769651 * 2 ^ 59
def prefixEnd_2769651 : Nat := 4983230072969 + 3 ^ 40 * 2769651 * 2
def baseEnd_2769651 : Nat := 1422162208205848461425113

theorem tailTrace_2769651 : CollatzResearch.WordTrace tailWord_2769651 prefixEnd_2769651 1422162208205848461425113 := by
  unfold tailWord_2769651
  simp only [CollatzResearch.WordTrace]
  refine ⟨101017470889034920576964807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67344980592689947051309871 101017470889034920576964807)
  ·
    refine ⟨151526206333552380865447211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101017470889034920576964807 151526206333552380865447211)
    ·
      refine ⟨227289309500328571298170817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151526206333552380865447211 227289309500328571298170817)
      ·
        refine ⟨170466982125246428473628113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227289309500328571298170817 170466982125246428473628113)
        ·
          refine ⟨127850236593934821355221085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170466982125246428473628113 127850236593934821355221085)
          ·
            refine ⟨47943838722725558008207907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127850236593934821355221085 47943838722725558008207907)
            ·
              refine ⟨71915758084088337012311861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47943838722725558008207907 71915758084088337012311861)
              ·
                refine ⟨6742102320383281594904237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71915758084088337012311861 6742102320383281594904237)
                ·
                  refine ⟨2528288370143730598089089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6742102320383281594904237 2528288370143730598089089)
                  ·
                    refine ⟨1896216277607797948566817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2528288370143730598089089 1896216277607797948566817)
                    ·
                      refine ⟨1422162208205848461425113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1896216277607797948566817 1422162208205848461425113)
                      ·
                        rfl

theorem cell23_2769651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3, 2, 2].length) (baseStart_2769651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769651 prefixEnd_2769651 := by exact prefixLift 2769651
  have htrace : WordTrace (prefixWord ++ tailWord_2769651) baseStart_2769651 baseEnd_2769651 := by
    simpa [prefixWord, tailWord_2769651, baseEnd_2769651] using wordTrace_append hprefix tailTrace_2769651
  have hstable : (prefixWord ++ tailWord_2769651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769651).length < 2 ^ (prefixWord ++ tailWord_2769651).sum := by decide
  have hdescent : baseEnd_2769651 < baseStart_2769651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769654 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_2769654 : Nat := 118140960795 + 2769654 * 2 ^ 59
def prefixEnd_2769654 : Nat := 4983230072969 + 3 ^ 40 * 2769654 * 2
def baseEnd_2769654 : Nat := 1422163748647811949687599

theorem tailTrace_2769654 : CollatzResearch.WordTrace tailWord_2769654 prefixEnd_2769654 1422163748647811949687599 := by
  unfold tailWord_2769654
  simp only [CollatzResearch.WordTrace]
  refine ⟨6313598769251503255582751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67345053538682701392882677 6313598769251503255582751)
  ·
    refine ⟨9470398153877254883374127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6313598769251503255582751 9470398153877254883374127)
    ·
      refine ⟨14205597230815882325061191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9470398153877254883374127 14205597230815882325061191)
      ·
        refine ⟨21308395846223823487591787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14205597230815882325061191 21308395846223823487591787)
        ·
          refine ⟨31962593769335735231387681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21308395846223823487591787 31962593769335735231387681)
          ·
            refine ⟨23971945327001801423540761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31962593769335735231387681 23971945327001801423540761)
            ·
              refine ⟨17978958995251351067655571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23971945327001801423540761 17978958995251351067655571)
              ·
                refine ⟨26968438492877026601483357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17978958995251351067655571 26968438492877026601483357)
                ·
                  refine ⟨10113164434828884975556259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26968438492877026601483357 10113164434828884975556259)
                  ·
                    refine ⟨15169746652243327463334389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10113164434828884975556259 15169746652243327463334389)
                    ·
                      refine ⟨1422163748647811949687599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15169746652243327463334389 1422163748647811949687599)
                      ·
                        rfl

theorem cell23_2769654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_2769654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769654 prefixEnd_2769654 := by exact prefixLift 2769654
  have htrace : WordTrace (prefixWord ++ tailWord_2769654) baseStart_2769654 baseEnd_2769654 := by
    simpa [prefixWord, tailWord_2769654, baseEnd_2769654] using wordTrace_append hprefix tailTrace_2769654
  have hstable : (prefixWord ++ tailWord_2769654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769654).length < 2 ^ (prefixWord ++ tailWord_2769654).sum := by decide
  have hdescent : baseEnd_2769654 < baseStart_2769654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769668 : List Nat := [2, 3, 2, 2, 1, 1, 3, 2, 3, 2, 2]
def baseStart_2769668 : Nat := 118140960795 + 2769668 * 2 ^ 59
def prefixEnd_2769668 : Nat := 4983230072969 + 3 ^ 40 * 2769668 * 2
def baseEnd_2769668 : Nat := 1422170937376974894912535

theorem tailTrace_2769668 : CollatzResearch.WordTrace tailWord_2769668 prefixEnd_2769668 1422170937376974894912535 := by
  unfold tailWord_2769668
  simp only [CollatzResearch.WordTrace]
  refine ⟨50509045464986666240166829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67345393953315554986889105 50509045464986666240166829)
  ·
    refine ⟨18940892049369999840062561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50509045464986666240166829 18940892049369999840062561)
    ·
      refine ⟨14205669037027499880046921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18940892049369999840062561 14205669037027499880046921)
      ·
        refine ⟨10654251777770624910035191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14205669037027499880046921 10654251777770624910035191)
        ·
          refine ⟨15981377666655937365052787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10654251777770624910035191 15981377666655937365052787)
          ·
            refine ⟨23972066499983906047579181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15981377666655937365052787 23972066499983906047579181)
            ·
              refine ⟨8989524937493964767842193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23972066499983906047579181 8989524937493964767842193)
              ·
                refine ⟨6742143703120473575881645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8989524937493964767842193 6742143703120473575881645)
                ·
                  refine ⟨2528303888670177590955617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6742143703120473575881645 2528303888670177590955617)
                  ·
                    refine ⟨1896227916502633193216713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2528303888670177590955617 1896227916502633193216713)
                    ·
                      refine ⟨1422170937376974894912535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1896227916502633193216713 1422170937376974894912535)
                      ·
                        rfl

theorem cell23_2769668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_2769668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769668 prefixEnd_2769668 := by exact prefixLift 2769668
  have htrace : WordTrace (prefixWord ++ tailWord_2769668) baseStart_2769668 baseEnd_2769668 := by
    simpa [prefixWord, tailWord_2769668, baseEnd_2769668] using wordTrace_append hprefix tailTrace_2769668
  have hstable : (prefixWord ++ tailWord_2769668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769668).length < 2 ^ (prefixWord ++ tailWord_2769668).sum := by decide
  have hdescent : baseEnd_2769668 < baseStart_2769668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769671 : List Nat := [1, 1, 4, 4, 1, 1, 2, 1, 3, 2, 3]
def baseStart_2769671 : Nat := 118140960795 + 2769671 * 2 ^ 59
def prefixEnd_2769671 : Nat := 4983230072969 + 3 ^ 40 * 2769671 * 2
def baseEnd_2769671 : Nat := 1422172477818938383175021

theorem tailTrace_2769671 : CollatzResearch.WordTrace tailWord_2769671 prefixEnd_2769671 1422172477818938383175021 := by
  unfold tailWord_2769671
  simp only [CollatzResearch.WordTrace]
  refine ⟨101018200348962463992692867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67345466899308309328461911 101018200348962463992692867)
  ·
    refine ⟨151527300523443695989039301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101018200348962463992692867 151527300523443695989039301)
    ·
      refine ⟨28411368848145692997944869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151527300523443695989039301 28411368848145692997944869)
      ·
        refine ⟨5327131659027317437114663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28411368848145692997944869 5327131659027317437114663)
        ·
          refine ⟨7990697488540976155671995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5327131659027317437114663 7990697488540976155671995)
          ·
            refine ⟨11986046232811464233507993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7990697488540976155671995 11986046232811464233507993)
            ·
              refine ⟨8989534674608598175130995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11986046232811464233507993 8989534674608598175130995)
              ·
                refine ⟨13484302011912897262696493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8989534674608598175130995 13484302011912897262696493)
                ·
                  refine ⟨5056613254467336473511185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13484302011912897262696493 5056613254467336473511185)
                  ·
                    refine ⟨3792459940850502355133389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5056613254467336473511185 3792459940850502355133389)
                    ·
                      refine ⟨1422172477818938383175021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3792459940850502355133389 1422172477818938383175021)
                      ·
                        rfl

theorem cell23_2769671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_2769671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769671 prefixEnd_2769671 := by exact prefixLift 2769671
  have htrace : WordTrace (prefixWord ++ tailWord_2769671) baseStart_2769671 baseEnd_2769671 := by
    simpa [prefixWord, tailWord_2769671, baseEnd_2769671] using wordTrace_append hprefix tailTrace_2769671
  have hstable : (prefixWord ++ tailWord_2769671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769671).length < 2 ^ (prefixWord ++ tailWord_2769671).sum := by decide
  have hdescent : baseEnd_2769671 < baseStart_2769671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769674 : List Nat := [3, 1, 2, 2, 1, 2, 5, 7]
def baseStart_2769674 : Nat := 118140960795 + 2769674 * 2 ^ 59
def prefixEnd_2769674 : Nat := 4983230072969 + 3 ^ 40 * 2769674 * 2
def baseEnd_2769674 : Nat := 52673111787440810053241

theorem tailTrace_2769674 : CollatzResearch.WordTrace tailWord_2769674 prefixEnd_2769674 52673111787440810053241 := by
  unfold tailWord_2769674
  simp only [CollatzResearch.WordTrace]
  refine ⟨25254577441987898876263019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67345539845301063670034717 25254577441987898876263019)
  ·
    refine ⟨37881866162981848314394529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25254577441987898876263019 37881866162981848314394529)
    ·
      refine ⟨28411399622236386235795897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37881866162981848314394529 28411399622236386235795897)
      ·
        refine ⟨21308549716677289676846923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28411399622236386235795897 21308549716677289676846923)
        ·
          refine ⟨31962824575015934515270385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21308549716677289676846923 31962824575015934515270385)
          ·
            refine ⟨23972118431261950886452789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31962824575015934515270385 23972118431261950886452789)
            ·
              refine ⟨2247386102930807895604949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23972118431261950886452789 2247386102930807895604949)
              ·
                refine ⟨52673111787440810053241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2247386102930807895604949 52673111787440810053241)
                ·
                  rfl

theorem cell23_2769674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 7].length) (baseStart_2769674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769674 prefixEnd_2769674 := by exact prefixLift 2769674
  have htrace : WordTrace (prefixWord ++ tailWord_2769674) baseStart_2769674 baseEnd_2769674 := by
    simpa [prefixWord, tailWord_2769674, baseEnd_2769674] using wordTrace_append hprefix tailTrace_2769674
  have hstable : (prefixWord ++ tailWord_2769674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769674).length < 2 ^ (prefixWord ++ tailWord_2769674).sum := by decide
  have hdescent : baseEnd_2769674 < baseStart_2769674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769682 : List Nat := [3, 2, 4, 1, 3, 1, 2, 1, 1, 5]
def baseStart_2769682 : Nat := 118140960795 + 2769682 * 2 ^ 59
def prefixEnd_2769682 : Nat := 4983230072969 + 3 ^ 40 * 2769682 * 2
def baseEnd_2769682 : Nat := 474059375368712613379157

theorem tailTrace_2769682 : CollatzResearch.WordTrace tailWord_2769682 prefixEnd_2769682 474059375368712613379157 := by
  unfold tailWord_2769682
  simp only [CollatzResearch.WordTrace]
  refine ⟨25254650387980653217835825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67345734367948408580895533 25254650387980653217835825)
  ·
    refine ⟨18940987790985489913376869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25254650387980653217835825 18940987790985489913376869)
    ·
      refine ⟨3551435210809779358758163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18940987790985489913376869 3551435210809779358758163)
      ·
        refine ⟨5327152816214669038137245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3551435210809779358758163 5327152816214669038137245)
        ·
          refine ⟨1997682306080500889301467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5327152816214669038137245 1997682306080500889301467)
          ·
            refine ⟨2996523459120751333952201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1997682306080500889301467 2996523459120751333952201)
            ·
              refine ⟨2247392594340563500464151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2996523459120751333952201 2247392594340563500464151)
              ·
                refine ⟨3371088891510845250696227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2247392594340563500464151 3371088891510845250696227)
                ·
                  refine ⟨5056633337266267876044341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3371088891510845250696227 5056633337266267876044341)
                  ·
                    refine ⟨474059375368712613379157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5056633337266267876044341 474059375368712613379157)
                    ·
                      rfl

theorem cell23_2769682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_2769682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769682 prefixEnd_2769682 := by exact prefixLift 2769682
  have htrace : WordTrace (prefixWord ++ tailWord_2769682) baseStart_2769682 baseEnd_2769682 := by
    simpa [prefixWord, tailWord_2769682, baseEnd_2769682] using wordTrace_append hprefix tailTrace_2769682
  have hstable : (prefixWord ++ tailWord_2769682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769682).length < 2 ^ (prefixWord ++ tailWord_2769682).sum := by decide
  have hdescent : baseEnd_2769682 < baseStart_2769682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769685 : List Nat := [1, 3, 2, 1, 2, 2, 4, 3, 1, 2, 2]
def baseStart_2769685 : Nat := 118140960795 + 2769685 * 2 ^ 59
def prefixEnd_2769685 : Nat := 4983230072969 + 3 ^ 40 * 2769685 * 2
def baseEnd_2769685 : Nat := 1422179666548101328399957

theorem tailTrace_2769685 : CollatzResearch.WordTrace tailWord_2769685 prefixEnd_2769685 1422179666548101328399957 := by
  unfold tailWord_2769685
  simp only [CollatzResearch.WordTrace]
  refine ⟨101018710970911744383702509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67345807313941162922468339 101018710970911744383702509)
  ·
    refine ⟨37882016614091904143888441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101018710970911744383702509 37882016614091904143888441)
    ·
      refine ⟨28411512460568928107916331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37882016614091904143888441 28411512460568928107916331)
      ·
        refine ⟨42617268690853392161874497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28411512460568928107916331 42617268690853392161874497)
        ·
          refine ⟨31962951518140044121405873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42617268690853392161874497 31962951518140044121405873)
          ·
            refine ⟨23972213638605033091054405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31962951518140044121405873 23972213638605033091054405)
            ·
              refine ⟨4494790057238443704572701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23972213638605033091054405 4494790057238443704572701)
              ·
                refine ⟨1685546271464416389214763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4494790057238443704572701 1685546271464416389214763)
                ·
                  refine ⟨2528319407196624583822145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1685546271464416389214763 2528319407196624583822145)
                  ·
                    refine ⟨1896239555397468437866609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2528319407196624583822145 1896239555397468437866609)
                    ·
                      refine ⟨1422179666548101328399957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1896239555397468437866609 1422179666548101328399957)
                      ·
                        rfl

theorem cell23_2769685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3, 1, 2, 2].length) (baseStart_2769685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769685 prefixEnd_2769685 := by exact prefixLift 2769685
  have htrace : WordTrace (prefixWord ++ tailWord_2769685) baseStart_2769685 baseEnd_2769685 := by
    simpa [prefixWord, tailWord_2769685, baseEnd_2769685] using wordTrace_append hprefix tailTrace_2769685
  have hstable : (prefixWord ++ tailWord_2769685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769685).length < 2 ^ (prefixWord ++ tailWord_2769685).sum := by decide
  have hdescent : baseEnd_2769685 < baseStart_2769685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769701 : List Nat := [1, 3, 1, 2, 3, 1, 3, 1, 4, 1, 3]
def baseStart_2769701 : Nat := 118140960795 + 2769701 * 2 ^ 59
def prefixEnd_2769701 : Nat := 4983230072969 + 3 ^ 40 * 2769701 * 2
def baseEnd_2769701 : Nat := 1422187882238573265799883

theorem tailTrace_2769701 : CollatzResearch.WordTrace tailWord_2769701 prefixEnd_2769701 1422187882238573265799883 := by
  unfold tailWord_2769701
  simp only [CollatzResearch.WordTrace]
  refine ⟨101019294538853779116284957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67346196359235852744189971 101019294538853779116284957)
  ·
    refine ⟨37882235452070167168606859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101019294538853779116284957 37882235452070167168606859)
    ·
      refine ⟨56823353178105250752910289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37882235452070167168606859 56823353178105250752910289)
      ·
        refine ⟨42617514883578938064682717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56823353178105250752910289 42617514883578938064682717)
        ·
          refine ⟨15981568081342101774256019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42617514883578938064682717 15981568081342101774256019)
          ·
            refine ⟨23972352122013152661384029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15981568081342101774256019 23972352122013152661384029)
            ·
              refine ⟨8989632045754932248019011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23972352122013152661384029 8989632045754932248019011)
              ·
                refine ⟨13484448068632398372028517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8989632045754932248019011 13484448068632398372028517)
                ·
                  refine ⟨2528334012868574694755347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13484448068632398372028517 2528334012868574694755347)
                  ·
                    refine ⟨3792501019302862042133021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2528334012868574694755347 3792501019302862042133021)
                    ·
                      refine ⟨1422187882238573265799883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3792501019302862042133021 1422187882238573265799883)
                      ·
                        rfl

theorem cell23_2769701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_2769701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769701 prefixEnd_2769701 := by exact prefixLift 2769701
  have htrace : WordTrace (prefixWord ++ tailWord_2769701) baseStart_2769701 baseEnd_2769701 := by
    simpa [prefixWord, tailWord_2769701, baseEnd_2769701] using wordTrace_append hprefix tailTrace_2769701
  have hstable : (prefixWord ++ tailWord_2769701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769701).length < 2 ^ (prefixWord ++ tailWord_2769701).sum := by decide
  have hdescent : baseEnd_2769701 < baseStart_2769701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769747 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 9]
def baseStart_2769747 : Nat := 118140960795 + 2769747 * 2 ^ 59
def prefixEnd_2769747 : Nat := 4983230072969 + 3 ^ 40 * 2769747 * 2
def baseEnd_2769747 : Nat := 158023500260964453980519

theorem tailTrace_2769747 : CollatzResearch.WordTrace tailWord_2769747 prefixEnd_2769747 158023500260964453980519 := by
  unfold tailWord_2769747
  simp only [CollatzResearch.WordTrace]
  refine ⟨101020972296687128972459495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67347314864458085981639663 101020972296687128972459495)
  ·
    refine ⟨151531458445030693458689243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101020972296687128972459495 151531458445030693458689243)
    ·
      refine ⟨227297187667546040188033865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151531458445030693458689243 227297187667546040188033865)
      ·
        refine ⟨170472890750659530141025399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227297187667546040188033865 170472890750659530141025399)
        ·
          refine ⟨255709336125989295211538099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170472890750659530141025399 255709336125989295211538099)
          ·
            refine ⟨383564004188983942817307149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255709336125989295211538099 383564004188983942817307149)
            ·
              refine ⟨143836501570868978556490181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 383564004188983942817307149 143836501570868978556490181)
              ·
                refine ⟨26969344044537933479341909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143836501570868978556490181 26969344044537933479341909)
                ·
                  refine ⟨158023500260964453980519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26969344044537933479341909 158023500260964453980519)
                  ·
                    rfl

theorem cell23_2769747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 9].length) (baseStart_2769747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769747 prefixEnd_2769747 := by exact prefixLift 2769747
  have htrace : WordTrace (prefixWord ++ tailWord_2769747) baseStart_2769747 baseEnd_2769747 := by
    simpa [prefixWord, tailWord_2769747, baseEnd_2769747] using wordTrace_append hprefix tailTrace_2769747
  have hstable : (prefixWord ++ tailWord_2769747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769747).length < 2 ^ (prefixWord ++ tailWord_2769747).sum := by decide
  have hdescent : baseEnd_2769747 < baseStart_2769747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769804 : List Nat := [2, 2, 1, 2, 1, 2, 3, 2, 1, 2, 5]
def baseStart_2769804 : Nat := 118140960795 + 2769804 * 2 ^ 59
def prefixEnd_2769804 : Nat := 4983230072969 + 3 ^ 40 * 2769804 * 2
def baseEnd_2769804 : Nat := 1422240770745986362811909

theorem tailTrace_2769804 : CollatzResearch.WordTrace tailWord_2769804 prefixEnd_2769804 1422240770745986362811909 := by
  unfold tailWord_2769804
  simp only [CollatzResearch.WordTrace]
  refine ⟨50511525628740313853642233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67348700838320418471522977 50511525628740313853642233)
  ·
    refine ⟨37883644221555235390231675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50511525628740313853642233 37883644221555235390231675)
    ·
      refine ⟨56825466332332853085347513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37883644221555235390231675 56825466332332853085347513)
      ·
        refine ⟨42619099749249639814010635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56825466332332853085347513 42619099749249639814010635)
        ·
          refine ⟨63928649623874459721015953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42619099749249639814010635 63928649623874459721015953)
          ·
            refine ⟨47946487217905844790761965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63928649623874459721015953 47946487217905844790761965)
            ·
              refine ⟨17979932706714691796535737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47946487217905844790761965 17979932706714691796535737)
              ·
                refine ⟨13484949530036018847401803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17979932706714691796535737 13484949530036018847401803)
                ·
                  refine ⟨20227424295054028271102705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13484949530036018847401803 20227424295054028271102705)
                  ·
                    refine ⟨15170568221290521203327029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20227424295054028271102705 15170568221290521203327029)
                    ·
                      refine ⟨1422240770745986362811909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15170568221290521203327029 1422240770745986362811909)
                      ·
                        rfl

theorem cell23_2769804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_2769804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769804 prefixEnd_2769804 := by exact prefixLift 2769804
  have htrace : WordTrace (prefixWord ++ tailWord_2769804) baseStart_2769804 baseEnd_2769804 := by
    simpa [prefixWord, tailWord_2769804, baseEnd_2769804] using wordTrace_append hprefix tailTrace_2769804
  have hstable : (prefixWord ++ tailWord_2769804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769804).length < 2 ^ (prefixWord ++ tailWord_2769804).sum := by decide
  have hdescent : baseEnd_2769804 < baseStart_2769804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769848 : List Nat := [2, 1, 2, 1, 2, 6, 1, 1, 2, 1, 4]
def baseStart_2769848 : Nat := 118140960795 + 2769848 * 2 ^ 59
def prefixEnd_2769848 : Nat := 4983230072969 + 3 ^ 40 * 2769848 * 2
def baseEnd_2769848 : Nat := 1422263363894784190661707

theorem tailTrace_2769848 : CollatzResearch.WordTrace tailWord_2769848 prefixEnd_2769848 1422263363894784190661707 := by
  unfold tailWord_2769848
  simp only [CollatzResearch.WordTrace]
  refine ⟨50512328034660611610943099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67349770712880815481257465 50512328034660611610943099)
  ·
    refine ⟨75768492051990917416414649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50512328034660611610943099 75768492051990917416414649)
    ·
      refine ⟨56826369038993188062310987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75768492051990917416414649 56826369038993188062310987)
      ·
        refine ⟨85239553558489782093466481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56826369038993188062310987 85239553558489782093466481)
        ·
          refine ⟨63929665168867336570099861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85239553558489782093466481 63929665168867336570099861)
          ·
            refine ⟨2996703054790656401723431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 63929665168867336570099861 2996703054790656401723431)
            ·
              refine ⟨4495054582185984602585147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2996703054790656401723431 4495054582185984602585147)
              ·
                refine ⟨6742581873278976903877721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4495054582185984602585147 6742581873278976903877721)
                ·
                  refine ⟨5056936404959232677908291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6742581873278976903877721 5056936404959232677908291)
                  ·
                    refine ⟨7585404607438849016862437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5056936404959232677908291 7585404607438849016862437)
                    ·
                      refine ⟨1422263363894784190661707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7585404607438849016862437 1422263363894784190661707)
                      ·
                        rfl

theorem cell23_2769848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 2, 1, 4].length) (baseStart_2769848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769848 prefixEnd_2769848 := by exact prefixLift 2769848
  have htrace : WordTrace (prefixWord ++ tailWord_2769848) baseStart_2769848 baseEnd_2769848 := by
    simpa [prefixWord, tailWord_2769848, baseEnd_2769848] using wordTrace_append hprefix tailTrace_2769848
  have hstable : (prefixWord ++ tailWord_2769848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769848).length < 2 ^ (prefixWord ++ tailWord_2769848).sum := by decide
  have hdescent : baseEnd_2769848 < baseStart_2769848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769871 : List Nat := [1, 1, 2, 1, 1, 6, 3, 2, 6]
def baseStart_2769871 : Nat := 118140960795 + 2769871 * 2 ^ 59
def prefixEnd_2769871 : Nat := 4983230072969 + 3 ^ 40 * 2769871 * 2
def baseEnd_2769871 : Nat := 158030574883315288963789

theorem tailTrace_2769871 : CollatzResearch.WordTrace tailWord_2769871 prefixEnd_2769871 158030574883315288963789 := by
  unfold tailWord_2769871
  simp only [CollatzResearch.WordTrace]
  refine ⟨101025494948237898149973467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67350329965491932099982311 101025494948237898149973467)
  ·
    refine ⟨151538242422356847224960201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101025494948237898149973467 151538242422356847224960201)
    ·
      refine ⟨113653681816767635418720151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151538242422356847224960201 113653681816767635418720151)
      ·
        refine ⟨170480522725151453128080227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113653681816767635418720151 170480522725151453128080227)
        ·
          refine ⟨255720784087727179692120341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170480522725151453128080227 255720784087727179692120341)
          ·
            refine ⟨11986911754112211548068141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 255720784087727179692120341 11986911754112211548068141)
            ·
              refine ⟨4495091907792079330525553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11986911754112211548068141 4495091907792079330525553)
              ·
                refine ⟨3371318930844059497894165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4495091907792079330525553 3371318930844059497894165)
                ·
                  refine ⟨158030574883315288963789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3371318930844059497894165 158030574883315288963789)
                  ·
                    rfl

theorem cell23_2769871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 6].length) (baseStart_2769871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769871 prefixEnd_2769871 := by exact prefixLift 2769871
  have htrace : WordTrace (prefixWord ++ tailWord_2769871) baseStart_2769871 baseEnd_2769871 := by
    simpa [prefixWord, tailWord_2769871, baseEnd_2769871] using wordTrace_append hprefix tailTrace_2769871
  have hstable : (prefixWord ++ tailWord_2769871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769871).length < 2 ^ (prefixWord ++ tailWord_2769871).sum := by decide
  have hdescent : baseEnd_2769871 < baseStart_2769871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769951 : List Nat := [1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 6]
def baseStart_2769951 : Nat := 118140960795 + 2769951 * 2 ^ 59
def prefixEnd_2769951 : Nat := 4983230072969 + 3 ^ 40 * 2769951 * 2
def baseEnd_2769951 : Nat := 1422316252402197287673733

theorem tailTrace_2769951 : CollatzResearch.WordTrace tailWord_2769951 prefixEnd_2769951 1422316252402197287673733 := by
  unfold tailWord_2769951
  simp only [CollatzResearch.WordTrace]
  refine ⟨101028412787948071812885707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67352275191965381208590471 101028412787948071812885707)
  ·
    refine ⟨151542619181922107719328561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101028412787948071812885707 151542619181922107719328561)
    ·
      refine ⟨113656964386441580789496421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151542619181922107719328561 113656964386441580789496421)
      ·
        refine ⟨21310680822457796398030579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113656964386441580789496421 21310680822457796398030579)
        ·
          refine ⟨31966021233686694597045869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21310680822457796398030579 31966021233686694597045869)
          ·
            refine ⟨11987257962632510473892201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31966021233686694597045869 11987257962632510473892201)
            ·
              refine ⟨8990443471974382855419151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11987257962632510473892201 8990443471974382855419151)
              ·
                refine ⟨13485665207961574283128727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8990443471974382855419151 13485665207961574283128727)
                ·
                  refine ⟨20228497811942361424693091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13485665207961574283128727 20228497811942361424693091)
                  ·
                    refine ⟨30342746717913542137039637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20228497811942361424693091 30342746717913542137039637)
                    ·
                      refine ⟨1422316252402197287673733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30342746717913542137039637 1422316252402197287673733)
                      ·
                        rfl

theorem cell23_2769951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_2769951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769951 prefixEnd_2769951 := by exact prefixLift 2769951
  have htrace : WordTrace (prefixWord ++ tailWord_2769951) baseStart_2769951 baseEnd_2769951 := by
    simpa [prefixWord, tailWord_2769951, baseEnd_2769951] using wordTrace_append hprefix tailTrace_2769951
  have hstable : (prefixWord ++ tailWord_2769951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769951).length < 2 ^ (prefixWord ++ tailWord_2769951).sum := by decide
  have hdescent : baseEnd_2769951 < baseStart_2769951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769952 : List Nat := [2, 1, 1, 7, 1, 2, 1, 2, 1, 5]
def baseStart_2769952 : Nat := 118140960795 + 2769952 * 2 ^ 59
def prefixEnd_2769952 : Nat := 4983230072969 + 3 ^ 40 * 2769952 * 2
def baseEnd_2769952 : Nat := 474105588627617261253743

theorem tailTrace_2769952 : CollatzResearch.WordTrace tailWord_2769952 prefixEnd_2769952 474105588627617261253743 := by
  unfold tailWord_2769952
  simp only [CollatzResearch.WordTrace]
  refine ⟨50514224630472224491836055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67352299507296299322448073 50514224630472224491836055)
  ·
    refine ⟨75771336945708336737754083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50514224630472224491836055 75771336945708336737754083)
    ·
      refine ⟨113657005418562505106631125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75771336945708336737754083 113657005418562505106631125)
      ·
        refine ⟨2663836064497558713436667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 113657005418562505106631125 2663836064497558713436667)
        ·
          refine ⟨3995754096746338070155001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2663836064497558713436667 3995754096746338070155001)
          ·
            refine ⟨2996815572559753552616251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3995754096746338070155001 2996815572559753552616251)
            ·
              refine ⟨4495223358839630328924377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2996815572559753552616251 4495223358839630328924377)
              ·
                refine ⟨3371417519129722746693283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4495223358839630328924377 3371417519129722746693283)
                ·
                  refine ⟨5057126278694584120039925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3371417519129722746693283 5057126278694584120039925)
                  ·
                    refine ⟨474105588627617261253743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5057126278694584120039925 474105588627617261253743)
                    ·
                      rfl

theorem cell23_2769952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 1, 5].length) (baseStart_2769952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769952 prefixEnd_2769952 := by exact prefixLift 2769952
  have htrace : WordTrace (prefixWord ++ tailWord_2769952) baseStart_2769952 baseEnd_2769952 := by
    simpa [prefixWord, tailWord_2769952, baseEnd_2769952] using wordTrace_append hprefix tailTrace_2769952
  have hstable : (prefixWord ++ tailWord_2769952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769952).length < 2 ^ (prefixWord ++ tailWord_2769952).sum := by decide
  have hdescent : baseEnd_2769952 < baseStart_2769952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769955 : List Nat := [1, 1, 1, 4, 3, 4, 1, 2, 1, 1, 4]
def baseStart_2769955 : Nat := 118140960795 + 2769955 * 2 ^ 59
def prefixEnd_2769955 : Nat := 4983230072969 + 3 ^ 40 * 2769955 * 2
def baseEnd_2769955 : Nat := 1422318306324815272023715

theorem tailTrace_2769955 : CollatzResearch.WordTrace tailWord_2769955 prefixEnd_2769955 1422318306324815272023715 := by
  unfold tailWord_2769955
  simp only [CollatzResearch.WordTrace]
  refine ⟨101028558679933580496031319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67352372453289053664020879 101028558679933580496031319)
  ·
    refine ⟨151542838019900370744046979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101028558679933580496031319 151542838019900370744046979)
    ·
      refine ⟨227314257029850556116070469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151542838019900370744046979 227314257029850556116070469)
      ·
        refine ⟨42621423193096979271763213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 227314257029850556116070469 42621423193096979271763213)
        ·
          refine ⟨15983033697411367226911205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42621423193096979271763213 15983033697411367226911205)
          ·
            refine ⟨2996818818264631355045851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15983033697411367226911205 2996818818264631355045851)
            ·
              refine ⟨4495228227396947032568777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2996818818264631355045851 4495228227396947032568777)
              ·
                refine ⟨3371421170547710274426583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4495228227396947032568777 3371421170547710274426583)
                ·
                  refine ⟨5057131755821565411639875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3371421170547710274426583 5057131755821565411639875)
                  ·
                    refine ⟨7585697633732348117459813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5057131755821565411639875 7585697633732348117459813)
                    ·
                      refine ⟨1422318306324815272023715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7585697633732348117459813 1422318306324815272023715)
                      ·
                        rfl

theorem cell23_2769955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_2769955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769955 prefixEnd_2769955 := by exact prefixLift 2769955
  have htrace : WordTrace (prefixWord ++ tailWord_2769955) baseStart_2769955 baseEnd_2769955 := by
    simpa [prefixWord, tailWord_2769955, baseEnd_2769955] using wordTrace_append hprefix tailTrace_2769955
  have hstable : (prefixWord ++ tailWord_2769955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769955).length < 2 ^ (prefixWord ++ tailWord_2769955).sum := by decide
  have hdescent : baseEnd_2769955 < baseStart_2769955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769982 : List Nat := [4, 2, 1, 3, 1, 2, 2, 2, 2, 4]
def baseStart_2769982 : Nat := 118140960795 + 2769982 * 2 ^ 59
def prefixEnd_2769982 : Nat := 4983230072969 + 3 ^ 40 * 2769982 * 2
def baseEnd_2769982 : Nat := 474110723434162222128697

theorem tailTrace_2769982 : CollatzResearch.WordTrace tailWord_2769982 prefixEnd_2769982 474110723434162222128697 := by
  unfold tailWord_2769982
  simp only [CollatzResearch.WordTrace]
  refine ⟨12628692931354470513408025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67353028967223842738176133 12628692931354470513408025)
  ·
    refine ⟨9471519698515852885056019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12628692931354470513408025 9471519698515852885056019)
    ·
      refine ⟨14207279547773779327584029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9471519698515852885056019 14207279547773779327584029)
      ·
        refine ⟨5327729830415167247844011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14207279547773779327584029 5327729830415167247844011)
        ·
          refine ⟨7991594745622750871766017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5327729830415167247844011 7991594745622750871766017)
          ·
            refine ⟨5993696059217063153824513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7991594745622750871766017 5993696059217063153824513)
            ·
              refine ⟨4495272044412797365368385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5993696059217063153824513 4495272044412797365368385)
              ·
                refine ⟨3371454033309598024026289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4495272044412797365368385 3371454033309598024026289)
                ·
                  refine ⟨2528590524982198518019717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3371454033309598024026289 2528590524982198518019717)
                  ·
                    refine ⟨474110723434162222128697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2528590524982198518019717 474110723434162222128697)
                    ·
                      rfl

theorem cell23_2769982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_2769982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769982 prefixEnd_2769982 := by exact prefixLift 2769982
  have htrace : WordTrace (prefixWord ++ tailWord_2769982) baseStart_2769982 baseEnd_2769982 := by
    simpa [prefixWord, tailWord_2769982, baseEnd_2769982] using wordTrace_append hprefix tailTrace_2769982
  have hstable : (prefixWord ++ tailWord_2769982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769982).length < 2 ^ (prefixWord ++ tailWord_2769982).sum := by decide
  have hdescent : baseEnd_2769982 < baseStart_2769982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769989 : List Nat := [1, 3, 1, 1, 1, 3, 6, 2, 1, 2, 2]
def baseStart_2769989 : Nat := 118140960795 + 2769989 * 2 ^ 59
def prefixEnd_2769989 : Nat := 4983230072969 + 3 ^ 40 * 2769989 * 2
def baseEnd_2769989 : Nat := 1422335764667068138998559

theorem tailTrace_2769989 : CollatzResearch.WordTrace tailWord_2769989 prefixEnd_2769989 1422335764667068138998559 := by
  unfold tailWord_2769989
  simp only [CollatzResearch.WordTrace]
  refine ⟨101029798761810404302769021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67353199174540269535179347 101029798761810404302769021)
  ·
    refine ⟨37886174535678901613538383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101029798761810404302769021 37886174535678901613538383)
    ·
      refine ⟨56829261803518352420307575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37886174535678901613538383 56829261803518352420307575)
      ·
        refine ⟨85243892705277528630461363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56829261803518352420307575 85243892705277528630461363)
        ·
          refine ⟨127865839057916292945692045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85243892705277528630461363 127865839057916292945692045)
          ·
            refine ⟨47949689646718609854634517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127865839057916292945692045 47949689646718609854634517)
            ·
              refine ⟨2247641702189934836935993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47949689646718609854634517 2247641702189934836935993)
              ·
                refine ⟨1685731276642451127701995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2247641702189934836935993 1685731276642451127701995)
                ·
                  refine ⟨2528596914963676691552993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1685731276642451127701995 2528596914963676691552993)
                  ·
                    refine ⟨1896447686222757518664745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2528596914963676691552993 1896447686222757518664745)
                    ·
                      refine ⟨1422335764667068138998559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1896447686222757518664745 1422335764667068138998559)
                      ·
                        rfl

theorem cell23_2769989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2, 1, 2, 2].length) (baseStart_2769989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769989 prefixEnd_2769989 := by exact prefixLift 2769989
  have htrace : WordTrace (prefixWord ++ tailWord_2769989) baseStart_2769989 baseEnd_2769989 := by
    simpa [prefixWord, tailWord_2769989, baseEnd_2769989] using wordTrace_append hprefix tailTrace_2769989
  have hstable : (prefixWord ++ tailWord_2769989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769989).length < 2 ^ (prefixWord ++ tailWord_2769989).sum := by decide
  have hdescent : baseEnd_2769989 < baseStart_2769989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769991 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 2, 7]
def baseStart_2769991 : Nat := 118140960795 + 2769991 * 2 ^ 59
def prefixEnd_2769991 : Nat := 4983230072969 + 3 ^ 40 * 2769991 * 2
def baseEnd_2769991 : Nat := 474112263876125710391183

theorem tailTrace_2769991 : CollatzResearch.WordTrace tailWord_2769991 prefixEnd_2769991 474112263876125710391183 := by
  unfold tailWord_2769991
  simp only [CollatzResearch.WordTrace]
  refine ⟨101029871707803158644341827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67353247805202105762894551 101029871707803158644341827)
  ·
    refine ⟨151544807561704737966512741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101029871707803158644341827 151544807561704737966512741)
    ·
      refine ⟨28414651417819638368721139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151544807561704737966512741 28414651417819638368721139)
      ·
        refine ⟨42621977126729457553081709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28414651417819638368721139 42621977126729457553081709)
        ·
          refine ⟨15983241422523546582405641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42621977126729457553081709 15983241422523546582405641)
          ·
            refine ⟨11987431066892659936804231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15983241422523546582405641 11987431066892659936804231)
            ·
              refine ⟨17981146600338989905206347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11987431066892659936804231 17981146600338989905206347)
              ·
                refine ⟨26971719900508484857809521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17981146600338989905206347 26971719900508484857809521)
                ·
                  refine ⟨20228789925381363643357141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26971719900508484857809521 20228789925381363643357141)
                  ·
                    refine ⟨474112263876125710391183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20228789925381363643357141 474112263876125710391183)
                    ·
                      rfl

theorem cell23_2769991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_2769991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2769991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2769991 prefixEnd_2769991 := by exact prefixLift 2769991
  have htrace : WordTrace (prefixWord ++ tailWord_2769991) baseStart_2769991 baseEnd_2769991 := by
    simpa [prefixWord, tailWord_2769991, baseEnd_2769991] using wordTrace_append hprefix tailTrace_2769991
  have hstable : (prefixWord ++ tailWord_2769991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769991).length < 2 ^ (prefixWord ++ tailWord_2769991).sum := by decide
  have hdescent : baseEnd_2769991 < baseStart_2769991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770005 : List Nat := [1, 3, 2, 2, 1, 2, 1, 5, 2, 1, 3]
def baseStart_2770005 : Nat := 118140960795 + 2770005 * 2 ^ 59
def prefixEnd_2770005 : Nat := 4983230072969 + 3 ^ 40 * 2770005 * 2
def baseEnd_2770005 : Nat := 1422343980357540076398485

theorem tailTrace_2770005 : CollatzResearch.WordTrace tailWord_2770005 prefixEnd_2770005 1422343980357540076398485 := by
  unfold tailWord_2770005
  simp only [CollatzResearch.WordTrace]
  refine ⟨101030382329752439035351469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67353588219834959356900979 101030382329752439035351469)
  ·
    refine ⟨37886393373657164638256801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101030382329752439035351469 37886393373657164638256801)
    ·
      refine ⟨28414795030242873478692601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37886393373657164638256801 28414795030242873478692601)
      ·
        refine ⟨21311096272682155109019451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28414795030242873478692601 21311096272682155109019451)
        ·
          refine ⟨31966644409023232663529177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21311096272682155109019451 31966644409023232663529177)
          ·
            refine ⟨23974983306767424497646883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31966644409023232663529177 23974983306767424497646883)
            ·
              refine ⟨35962474960151136746470325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23974983306767424497646883 35962474960151136746470325)
              ·
                refine ⟨3371482027514169069981593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35962474960151136746470325 3371482027514169069981593)
                ·
                  refine ⟨2528611520635626802486195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3371482027514169069981593 2528611520635626802486195)
                  ·
                    refine ⟨3792917280953440203729293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2528611520635626802486195 3792917280953440203729293)
                    ·
                      refine ⟨1422343980357540076398485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3792917280953440203729293 1422343980357540076398485)
                      ·
                        rfl

theorem cell23_2770005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_2770005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770005 prefixEnd_2770005 := by exact prefixLift 2770005
  have htrace : WordTrace (prefixWord ++ tailWord_2770005) baseStart_2770005 baseEnd_2770005 := by
    simpa [prefixWord, tailWord_2770005, baseEnd_2770005] using wordTrace_append hprefix tailTrace_2770005
  have hstable : (prefixWord ++ tailWord_2770005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770005).length < 2 ^ (prefixWord ++ tailWord_2770005).sum := by decide
  have hdescent : baseEnd_2770005 < baseStart_2770005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770006 : List Nat := [5, 2, 2, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_2770006 : Nat := 118140960795 + 2770006 * 2 ^ 59
def prefixEnd_2770006 : Nat := 4983230072969 + 3 ^ 40 * 2770006 * 2
def baseEnd_2770006 : Nat := 1422344493838194572485981

theorem tailTrace_2770006 : CollatzResearch.WordTrace tailWord_2770006 prefixEnd_2770006 1422344493838194572485981 := by
  unfold tailWord_2770006
  simp only [CollatzResearch.WordTrace]
  refine ⟨6314401175171801012883617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67353612535165877470758581 6314401175171801012883617)
  ·
    refine ⟨4735800881378850759662713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6314401175171801012883617 4735800881378850759662713)
    ·
      refine ⟨3551850661034138069747035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4735800881378850759662713 3551850661034138069747035)
      ·
        refine ⟨5327775991551207104620553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3551850661034138069747035 5327775991551207104620553)
        ·
          refine ⟨3995831993663405328465415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5327775991551207104620553 3995831993663405328465415)
          ·
            refine ⟨5993747990495107992698123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3995831993663405328465415 5993747990495107992698123)
            ·
              refine ⟨8990621985742661989047185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5993747990495107992698123 8990621985742661989047185)
              ·
                refine ⟨6742966489306996491785389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8990621985742661989047185 6742966489306996491785389)
                ·
                  refine ⟨2528612433490123684419521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6742966489306996491785389 2528612433490123684419521)
                  ·
                    refine ⟨1896459325117592763314641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2528612433490123684419521 1896459325117592763314641)
                    ·
                      refine ⟨1422344493838194572485981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1896459325117592763314641 1422344493838194572485981)
                      ·
                        rfl

theorem cell23_2770006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_2770006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770006 prefixEnd_2770006 := by exact prefixLift 2770006
  have htrace : WordTrace (prefixWord ++ tailWord_2770006) baseStart_2770006 baseEnd_2770006 := by
    simpa [prefixWord, tailWord_2770006, baseEnd_2770006] using wordTrace_append hprefix tailTrace_2770006
  have hstable : (prefixWord ++ tailWord_2770006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770006).length < 2 ^ (prefixWord ++ tailWord_2770006).sum := by decide
  have hdescent : baseEnd_2770006 < baseStart_2770006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770015 : List Nat := [1, 1, 2, 3, 1, 1, 4, 4, 1, 3, 2]
def baseStart_2770015 : Nat := 118140960795 + 2770015 * 2 ^ 59
def prefixEnd_2770015 : Nat := 4983230072969 + 3 ^ 40 * 2770015 * 2
def baseEnd_2770015 : Nat := 1422349115164085037273439

theorem tailTrace_2770015 : CollatzResearch.WordTrace tailWord_2770015 prefixEnd_2770015 1422349115164085037273439 := by
  unfold tailWord_2770015
  simp only [CollatzResearch.WordTrace]
  refine ⟨101030747059716210743215499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67353831373144140495476999 101030747059716210743215499)
  ·
    refine ⟨151546120589574316114823249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101030747059716210743215499 151546120589574316114823249)
    ·
      refine ⟨113659590442180737086117437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151546120589574316114823249 113659590442180737086117437)
      ·
        refine ⟨42622346415817776407294039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113659590442180737086117437 42622346415817776407294039)
        ·
          refine ⟨63933519623726664610941059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42622346415817776407294039 63933519623726664610941059)
          ·
            refine ⟨95900279435589996916411589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63933519623726664610941059 95900279435589996916411589)
            ·
              refine ⟨17981302394173124421827173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95900279435589996916411589 17981302394173124421827173)
              ·
                refine ⟨3371494198907460829092595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17981302394173124421827173 3371494198907460829092595)
                ·
                  refine ⟨5057241298361191243638893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3371494198907460829092595 5057241298361191243638893)
                  ·
                    refine ⟨1896465486885446716364585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5057241298361191243638893 1896465486885446716364585)
                    ·
                      refine ⟨1422349115164085037273439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1896465486885446716364585 1422349115164085037273439)
                      ·
                        rfl

theorem cell23_2770015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 3, 2].length) (baseStart_2770015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770015 prefixEnd_2770015 := by exact prefixLift 2770015
  have htrace : WordTrace (prefixWord ++ tailWord_2770015) baseStart_2770015 baseEnd_2770015 := by
    simpa [prefixWord, tailWord_2770015, baseEnd_2770015] using wordTrace_append hprefix tailTrace_2770015
  have hstable : (prefixWord ++ tailWord_2770015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770015).length < 2 ^ (prefixWord ++ tailWord_2770015).sum := by decide
  have hdescent : baseEnd_2770015 < baseStart_2770015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770021 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 1, 8]
def baseStart_2770021 : Nat := 118140960795 + 2770021 * 2 ^ 59
def prefixEnd_2770021 : Nat := 4983230072969 + 3 ^ 40 * 2770021 * 2
def baseEnd_2770021 : Nat := 474117398682670671266137

theorem tailTrace_2770021 : CollatzResearch.WordTrace tailWord_2770021 prefixEnd_2770021 474117398682670671266137 := by
  unfold tailWord_2770021
  simp only [CollatzResearch.WordTrace]
  refine ⟨101030965897694473767933917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67353977265129649178622611 101030965897694473767933917)
  ·
    refine ⟨37886612211635427662975219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101030965897694473767933917 37886612211635427662975219)
    ·
      refine ⟨56829918317453141494462829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37886612211635427662975219 56829918317453141494462829)
      ·
        refine ⟨21311219369044928060423561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56829918317453141494462829 21311219369044928060423561)
        ·
          refine ⟨15983414526783696045317671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21311219369044928060423561 15983414526783696045317671)
          ·
            refine ⟨23975121790175544067976507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15983414526783696045317671 23975121790175544067976507)
            ·
              refine ⟨35962682685263316101964761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23975121790175544067976507 35962682685263316101964761)
              ·
                refine ⟨26972012013947487076473571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35962682685263316101964761 26972012013947487076473571)
                ·
                  refine ⟨40458018020921230614710357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26972012013947487076473571 40458018020921230614710357)
                  ·
                    refine ⟨474117398682670671266137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40458018020921230614710357 474117398682670671266137)
                    ·
                      rfl

theorem cell23_2770021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_2770021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770021 prefixEnd_2770021 := by exact prefixLift 2770021
  have htrace : WordTrace (prefixWord ++ tailWord_2770021) baseStart_2770021 baseEnd_2770021 := by
    simpa [prefixWord, tailWord_2770021, baseEnd_2770021] using wordTrace_append hprefix tailTrace_2770021
  have hstable : (prefixWord ++ tailWord_2770021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770021).length < 2 ^ (prefixWord ++ tailWord_2770021).sum := by decide
  have hdescent : baseEnd_2770021 < baseStart_2770021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770031 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 5]
def baseStart_2770031 : Nat := 118140960795 + 2770031 * 2 ^ 59
def prefixEnd_2770031 : Nat := 4983230072969 + 3 ^ 40 * 2770031 * 2
def baseEnd_2770031 : Nat := 1422357330854556974673365

theorem tailTrace_2770031 : CollatzResearch.WordTrace tailWord_2770031 prefixEnd_2770031 1422357330854556974673365 := by
  unfold tailWord_2770031
  simp only [CollatzResearch.WordTrace]
  refine ⟨101031330627658245475797947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67354220418438830317198631 101031330627658245475797947)
  ·
    refine ⟨151546995941487368213696921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101031330627658245475797947 151546995941487368213696921)
    ·
      refine ⟨113660246956115526160272691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151546995941487368213696921 113660246956115526160272691)
      ·
        refine ⟨170490370434173289240409037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113660246956115526160272691 170490370434173289240409037)
        ·
          refine ⟨63933888912814983465153389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170490370434173289240409037 63933888912814983465153389)
          ·
            refine ⟨23975208342305618799432521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63933888912814983465153389 23975208342305618799432521)
            ·
              refine ⟨17981406256729214099574391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23975208342305618799432521 17981406256729214099574391)
              ·
                refine ⟨26972109385093821149361587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17981406256729214099574391 26972109385093821149361587)
                ·
                  refine ⟨40458164077640731724042381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26972109385093821149361587 40458164077640731724042381)
                  ·
                    refine ⟨15171811529115274396515893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40458164077640731724042381 15171811529115274396515893)
                    ·
                      refine ⟨1422357330854556974673365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15171811529115274396515893 1422357330854556974673365)
                      ·
                        rfl

theorem cell23_2770031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 5].length) (baseStart_2770031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770031 prefixEnd_2770031 := by exact prefixLift 2770031
  have htrace : WordTrace (prefixWord ++ tailWord_2770031) baseStart_2770031 baseEnd_2770031 := by
    simpa [prefixWord, tailWord_2770031, baseEnd_2770031] using wordTrace_append hprefix tailTrace_2770031
  have hstable : (prefixWord ++ tailWord_2770031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770031).length < 2 ^ (prefixWord ++ tailWord_2770031).sum := by decide
  have hdescent : baseEnd_2770031 < baseStart_2770031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770038 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 4, 6]
def baseStart_2770038 : Nat := 118140960795 + 2770038 * 2 ^ 59
def prefixEnd_2770038 : Nat := 4983230072969 + 3 ^ 40 * 2770038 * 2
def baseEnd_2770038 : Nat := 474120308406379482428611

theorem tailTrace_2770038 : CollatzResearch.WordTrace tailWord_2770038 prefixEnd_2770038 474120308406379482428611 := by
  unfold tailWord_2770038
  simp only [CollatzResearch.WordTrace]
  refine ⟨6314474121164555354456423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67354390625755257114201845 6314474121164555354456423)
  ·
    refine ⟨9471711181746833031684635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6314474121164555354456423 9471711181746833031684635)
    ·
      refine ⟨14207566772620249547526953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9471711181746833031684635 14207566772620249547526953)
      ·
        refine ⟨10655675079465187160645215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14207566772620249547526953 10655675079465187160645215)
        ·
          refine ⟨15983512619197780740967823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10655675079465187160645215 15983512619197780740967823)
          ·
            refine ⟨23975268928796671111451735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15983512619197780740967823 23975268928796671111451735)
            ·
              refine ⟨35962903393195006667177603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23975268928796671111451735 35962903393195006667177603)
              ·
                refine ⟨53944355089792510000766405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35962903393195006667177603 53944355089792510000766405)
                ·
                  refine ⟨10114566579336095625143701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53944355089792510000766405 10114566579336095625143701)
                  ·
                    refine ⟨474120308406379482428611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10114566579336095625143701 474120308406379482428611)
                    ·
                      rfl

theorem cell23_2770038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_2770038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770038 prefixEnd_2770038 := by exact prefixLift 2770038
  have htrace : WordTrace (prefixWord ++ tailWord_2770038) baseStart_2770038 baseEnd_2770038 := by
    simpa [prefixWord, tailWord_2770038, baseEnd_2770038] using wordTrace_append hprefix tailTrace_2770038
  have hstable : (prefixWord ++ tailWord_2770038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770038).length < 2 ^ (prefixWord ++ tailWord_2770038).sum := by decide
  have hdescent : baseEnd_2770038 < baseStart_2770038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770058 : List Nat := [3, 1, 2, 3, 1, 1, 1, 3, 2, 2, 4]
def baseStart_2770058 : Nat := 118140960795 + 2770058 * 2 ^ 59
def prefixEnd_2770058 : Nat := 4983230072969 + 3 ^ 40 * 2770058 * 2
def baseEnd_2770058 : Nat := 1422371194832228369035741

theorem tailTrace_2770058 : CollatzResearch.WordTrace tailWord_2770058 prefixEnd_2770058 1422371194832228369035741 := by
  unfold tailWord_2770058
  simp only [CollatzResearch.WordTrace]
  refine ⟨25258078849640107271757707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67354876932373619391353885 25258078849640107271757707)
  ·
    refine ⟨37887118274460160907636561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25258078849640107271757707 37887118274460160907636561)
    ·
      refine ⟨28415338705845120680727421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37887118274460160907636561 28415338705845120680727421)
      ·
        refine ⟨10655752014691920255272783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28415338705845120680727421 10655752014691920255272783)
        ·
          refine ⟨15983628022037880382909175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10655752014691920255272783 15983628022037880382909175)
          ·
            refine ⟨23975442033056820574363763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15983628022037880382909175 23975442033056820574363763)
            ·
              refine ⟨35963163049585230861545645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23975442033056820574363763 35963163049585230861545645)
              ·
                refine ⟨13486186143594461573079617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35963163049585230861545645 13486186143594461573079617)
                ·
                  refine ⟨10114639607695846179809713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13486186143594461573079617 10114639607695846179809713)
                  ·
                    refine ⟨7585979705771884634857285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10114639607695846179809713 7585979705771884634857285)
                    ·
                      refine ⟨1422371194832228369035741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7585979705771884634857285 1422371194832228369035741)
                      ·
                        rfl

theorem cell23_2770058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_2770058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770058 prefixEnd_2770058 := by exact prefixLift 2770058
  have htrace : WordTrace (prefixWord ++ tailWord_2770058) baseStart_2770058 baseEnd_2770058 := by
    simpa [prefixWord, tailWord_2770058, baseEnd_2770058] using wordTrace_append hprefix tailTrace_2770058
  have hstable : (prefixWord ++ tailWord_2770058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770058).length < 2 ^ (prefixWord ++ tailWord_2770058).sum := by decide
  have hdescent : baseEnd_2770058 < baseStart_2770058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770062 : List Nat := [4, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2]
def baseStart_2770062 : Nat := 118140960795 + 2770062 * 2 ^ 59
def prefixEnd_2770062 : Nat := 4983230072969 + 3 ^ 40 * 2770062 * 2
def baseEnd_2770062 : Nat := 1422373248754846353385723

theorem tailTrace_2770062 : CollatzResearch.WordTrace tailWord_2770062 prefixEnd_2770062 1422373248754846353385723 := by
  unfold tailWord_2770062
  simp only [CollatzResearch.WordTrace]
  refine ⟨12629057661318242221272055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67354974193697291846784293 12629057661318242221272055)
  ·
    refine ⟨18943586491977363331908083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12629057661318242221272055 18943586491977363331908083)
    ·
      refine ⟨28415379737966044997862125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18943586491977363331908083 28415379737966044997862125)
      ·
        refine ⟨10655767401737266874198297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28415379737966044997862125 10655767401737266874198297)
        ·
          refine ⟨7991825551302950155648723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10655767401737266874198297 7991825551302950155648723)
          ·
            refine ⟨11987738326954425233473085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7991825551302950155648723 11987738326954425233473085)
            ·
              refine ⟨4495401872607909462552407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11987738326954425233473085 4495401872607909462552407)
              ·
                refine ⟨6743102808911864193828611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4495401872607909462552407 6743102808911864193828611)
                ·
                  refine ⟨10114654213367796290742917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6743102808911864193828611 10114654213367796290742917)
                  ·
                    refine ⟨1896497665006461804514297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10114654213367796290742917 1896497665006461804514297)
                    ·
                      refine ⟨1422373248754846353385723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1896497665006461804514297 1422373248754846353385723)
                      ·
                        rfl

theorem cell23_2770062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_2770062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770062 prefixEnd_2770062 := by exact prefixLift 2770062
  have htrace : WordTrace (prefixWord ++ tailWord_2770062) baseStart_2770062 baseEnd_2770062 := by
    simpa [prefixWord, tailWord_2770062, baseEnd_2770062] using wordTrace_append hprefix tailTrace_2770062
  have hstable : (prefixWord ++ tailWord_2770062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770062).length < 2 ^ (prefixWord ++ tailWord_2770062).sum := by decide
  have hdescent : baseEnd_2770062 < baseStart_2770062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770085 : List Nat := [1, 3, 1, 2, 1, 4, 3, 3, 5]
def baseStart_2770085 : Nat := 118140960795 + 2770085 * 2 ^ 59
def prefixEnd_2770085 : Nat := 4983230072969 + 3 ^ 40 * 2770085 * 2
def baseEnd_2770085 : Nat := 158042784312211084822013

theorem tailTrace_2770085 : CollatzResearch.WordTrace tailWord_2770085 prefixEnd_2770085 158042784312211084822013 := by
  unfold tailWord_2770085
  simp only [CollatzResearch.WordTrace]
  refine ⟨101033300169462612698263709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67355533446308408465509139 101033300169462612698263709)
  ·
    refine ⟨37887487563548479761848891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101033300169462612698263709 37887487563548479761848891)
    ·
      refine ⟨56831231345322719642773337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37887487563548479761848891 56831231345322719642773337)
      ·
        refine ⟨42623423508992039732080003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56831231345322719642773337 42623423508992039732080003)
        ·
          refine ⟨63935135263488059598120005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42623423508992039732080003 63935135263488059598120005)
          ·
            refine ⟨11987837861904011174647501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63935135263488059598120005 11987837861904011174647501)
            ·
              refine ⟨4495439198214004190492813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11987837861904011174647501 4495439198214004190492813)
              ·
                refine ⟨1685789699330251571434805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4495439198214004190492813 1685789699330251571434805)
                ·
                  refine ⟨158042784312211084822013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1685789699330251571434805 158042784312211084822013)
                  ·
                    rfl

theorem cell23_2770085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3, 5].length) (baseStart_2770085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770085 prefixEnd_2770085 := by exact prefixLift 2770085
  have htrace : WordTrace (prefixWord ++ tailWord_2770085) baseStart_2770085 baseEnd_2770085 := by
    simpa [prefixWord, tailWord_2770085, baseEnd_2770085] using wordTrace_append hprefix tailTrace_2770085
  have hstable : (prefixWord ++ tailWord_2770085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770085).length < 2 ^ (prefixWord ++ tailWord_2770085).sum := by decide
  have hdescent : baseEnd_2770085 < baseStart_2770085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770098 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 4, 5]
def baseStart_2770098 : Nat := 118140960795 + 2770098 * 2 ^ 59
def prefixEnd_2770098 : Nat := 4983230072969 + 3 ^ 40 * 2770098 * 2
def baseEnd_2770098 : Nat := 474130578019469404178519

theorem tailTrace_2770098 : CollatzResearch.WordTrace tailWord_2770098 prefixEnd_2770098 474130578019469404178519 := by
  unfold tailWord_2770098
  simp only [CollatzResearch.WordTrace]
  refine ⟨25258443579603878979621737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67355849545610343945657965 25258443579603878979621737)
  ·
    refine ⟨18943832684702909234716303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25258443579603878979621737 18943832684702909234716303)
    ·
      refine ⟨28415749027054363852074455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18943832684702909234716303 28415749027054363852074455)
      ·
        refine ⟨42623623540581545778111683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28415749027054363852074455 42623623540581545778111683)
        ·
          refine ⟨63935435310872318667167525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42623623540581545778111683 63935435310872318667167525)
          ·
            refine ⟨11987894120788559750093911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63935435310872318667167525 11987894120788559750093911)
            ·
              refine ⟨17981841181182839625140867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11987894120788559750093911 17981841181182839625140867)
              ·
                refine ⟨26972761771774259437711301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17981841181182839625140867 26972761771774259437711301)
                ·
                  refine ⟨5057392832207673644570869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26972761771774259437711301 5057392832207673644570869)
                  ·
                    refine ⟨474130578019469404178519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5057392832207673644570869 474130578019469404178519)
                    ·
                      rfl

theorem cell23_2770098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_2770098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770098 prefixEnd_2770098 := by exact prefixLift 2770098
  have htrace : WordTrace (prefixWord ++ tailWord_2770098) baseStart_2770098 baseEnd_2770098 := by
    simpa [prefixWord, tailWord_2770098, baseEnd_2770098] using wordTrace_append hprefix tailTrace_2770098
  have hstable : (prefixWord ++ tailWord_2770098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770098).length < 2 ^ (prefixWord ++ tailWord_2770098).sum := by decide
  have hdescent : baseEnd_2770098 < baseStart_2770098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770108 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 1, 1, 7]
def baseStart_2770108 : Nat := 118140960795 + 2770108 * 2 ^ 59
def prefixEnd_2770108 : Nat := 4983230072969 + 3 ^ 40 * 2770108 * 2
def baseEnd_2770108 : Nat := 1422396868864953173410511

theorem tailTrace_2770108 : CollatzResearch.WordTrace tailWord_2770108 prefixEnd_2770108 1422396868864953173410511 := by
  unfold tailWord_2770108
  simp only [CollatzResearch.WordTrace]
  refine ⟨50517069524189643813175489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67356092698919525084233985 50517069524189643813175489)
  ·
    refine ⟨37887802143142232859881617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50517069524189643813175489 37887802143142232859881617)
    ·
      refine ⟨28415851607356674644911213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37887802143142232859881617 28415851607356674644911213)
      ·
        refine ⟨10655944352758752991841705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28415851607356674644911213 10655944352758752991841705)
        ·
          refine ⟨7991958264569064743881279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10655944352758752991841705 7991958264569064743881279)
          ·
            refine ⟨11987937396853597115821919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7991958264569064743881279 11987937396853597115821919)
            ·
              refine ⟨17981906095280395673732879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11987937396853597115821919 17981906095280395673732879)
              ·
                refine ⟨26972859142920593510599319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17981906095280395673732879 26972859142920593510599319)
                ·
                  refine ⟨40459288714380890265898979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26972859142920593510599319 40459288714380890265898979)
                  ·
                    refine ⟨60688933071571335398848469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40459288714380890265898979 60688933071571335398848469)
                    ·
                      refine ⟨1422396868864953173410511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60688933071571335398848469 1422396868864953173410511)
                      ·
                        rfl

theorem cell23_2770108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_2770108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770108 prefixEnd_2770108 := by exact prefixLift 2770108
  have htrace : WordTrace (prefixWord ++ tailWord_2770108) baseStart_2770108 baseEnd_2770108 := by
    simpa [prefixWord, tailWord_2770108, baseEnd_2770108] using wordTrace_append hprefix tailTrace_2770108
  have hstable : (prefixWord ++ tailWord_2770108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770108).length < 2 ^ (prefixWord ++ tailWord_2770108).sum := by decide
  have hdescent : baseEnd_2770108 < baseStart_2770108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770113 : List Nat := [1, 2, 6, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_2770113 : Nat := 118140960795 + 2770113 * 2 ^ 59
def prefixEnd_2770113 : Nat := 4983230072969 + 3 ^ 40 * 2770113 * 2
def baseEnd_2770113 : Nat := 1422399436268225653847989

theorem tailTrace_2770113 : CollatzResearch.WordTrace tailWord_2770113 prefixEnd_2770113 1422399436268225653847989 := by
  unfold tailWord_2770113
  simp only [CollatzResearch.WordTrace]
  refine ⟨101034321413361173480282993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67356214275574115653521995 101034321413361173480282993)
  ·
    refine ⟨75775741060020880110212245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101034321413361173480282993 75775741060020880110212245)
    ·
      refine ⟨3551987862188478755166199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 75775741060020880110212245 3551987862188478755166199)
      ·
        refine ⟨5327981793282718132749299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3551987862188478755166199 5327981793282718132749299)
        ·
          refine ⟨7991972689924077199123949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5327981793282718132749299 7991972689924077199123949)
          ·
            refine ⟨2996989758721528949671481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7991972689924077199123949 2996989758721528949671481)
            ·
              refine ⟨2247742319041146712253611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2996989758721528949671481 2247742319041146712253611)
              ·
                refine ⟨3371613478561720068380417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2247742319041146712253611 3371613478561720068380417)
                ·
                  refine ⟨2528710108921290051285313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3371613478561720068380417 2528710108921290051285313)
                  ·
                    refine ⟨1896532581690967538463985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2528710108921290051285313 1896532581690967538463985)
                    ·
                      refine ⟨1422399436268225653847989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1896532581690967538463985 1422399436268225653847989)
                      ·
                        rfl

theorem cell23_2770113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_2770113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770113 prefixEnd_2770113 := by exact prefixLift 2770113
  have htrace : WordTrace (prefixWord ++ tailWord_2770113) baseStart_2770113 baseEnd_2770113 := by
    simpa [prefixWord, tailWord_2770113, baseEnd_2770113] using wordTrace_append hprefix tailTrace_2770113
  have hstable : (prefixWord ++ tailWord_2770113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770113).length < 2 ^ (prefixWord ++ tailWord_2770113).sum := by decide
  have hdescent : baseEnd_2770113 < baseStart_2770113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770121 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 9]
def baseStart_2770121 : Nat := 118140960795 + 2770121 * 2 ^ 59
def prefixEnd_2770121 : Nat := 4983230072969 + 3 ^ 40 * 2770121 * 2
def baseEnd_2770121 : Nat := 1422403544113461622547951

theorem tailTrace_2770121 : CollatzResearch.WordTrace tailWord_2770121 prefixEnd_2770121 1422403544113461622547951 := by
  unfold tailWord_2770121
  simp only [CollatzResearch.WordTrace]
  refine ⟨101034613197332190846574217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67356408798221460564382811 101034613197332190846574217)
  ·
    refine ⟨75775959897999143134930663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101034613197332190846574217 75775959897999143134930663)
    ·
      refine ⟨113663939846998714702395995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75775959897999143134930663 113663939846998714702395995)
      ·
        refine ⟨170495909770498072053593993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113663939846998714702395995 170495909770498072053593993)
        ·
          refine ⟨127871932327873554040195495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170495909770498072053593993 127871932327873554040195495)
          ·
            refine ⟨191807898491810331060293243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127871932327873554040195495 191807898491810331060293243)
            ·
              refine ⟨287711847737715496590439865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191807898491810331060293243 287711847737715496590439865)
              ·
                refine ⟨215783885803286622442829899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 287711847737715496590439865 215783885803286622442829899)
                ·
                  refine ⟨323675828704929933664244849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215783885803286622442829899 323675828704929933664244849)
                  ·
                    refine ⟨242756871528697450248183637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 323675828704929933664244849 242756871528697450248183637)
                    ·
                      refine ⟨1422403544113461622547951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 242756871528697450248183637 1422403544113461622547951)
                      ·
                        rfl

theorem cell23_2770121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_2770121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770121 prefixEnd_2770121 := by exact prefixLift 2770121
  have htrace : WordTrace (prefixWord ++ tailWord_2770121) baseStart_2770121 baseEnd_2770121 := by
    simpa [prefixWord, tailWord_2770121, baseEnd_2770121] using wordTrace_append hprefix tailTrace_2770121
  have hstable : (prefixWord ++ tailWord_2770121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770121).length < 2 ^ (prefixWord ++ tailWord_2770121).sum := by decide
  have hdescent : baseEnd_2770121 < baseStart_2770121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770155 : List Nat := [1, 1, 1, 1, 2, 6, 2, 2, 2, 2, 3]
def baseStart_2770155 : Nat := 118140960795 + 2770155 * 2 ^ 59
def prefixEnd_2770155 : Nat := 4983230072969 + 3 ^ 40 * 2770155 * 2
def baseEnd_2770155 : Nat := 1422421002455714489522795

theorem tailTrace_2770155 : CollatzResearch.WordTrace tailWord_2770155 prefixEnd_2770155 1422421002455714489522795 := by
  unfold tailWord_2770155
  simp only [CollatzResearch.WordTrace]
  refine ⟨101035853279209014653311919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67357235519472676435541279 101035853279209014653311919)
  ·
    refine ⟨151553779918813521979967879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101035853279209014653311919 151553779918813521979967879)
    ·
      refine ⟨227330669878220282969951819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151553779918813521979967879 227330669878220282969951819)
      ·
        refine ⟨340996004817330424454927729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227330669878220282969951819 340996004817330424454927729)
        ·
          refine ⟨255747003612997818341195797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340996004817330424454927729 255747003612997818341195797)
          ·
            refine ⟨11988140794359272734743553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 255747003612997818341195797 11988140794359272734743553)
            ·
              refine ⟨8991105595769454551057665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11988140794359272734743553 8991105595769454551057665)
              ·
                refine ⟨6743329196827090913293249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8991105595769454551057665 6743329196827090913293249)
                ·
                  refine ⟨5057496897620318184969937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6743329196827090913293249 5057496897620318184969937)
                  ·
                    refine ⟨3793122673215238638727453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5057496897620318184969937 3793122673215238638727453)
                    ·
                      refine ⟨1422421002455714489522795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3793122673215238638727453 1422421002455714489522795)
                      ·
                        rfl

theorem cell23_2770155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2, 3].length) (baseStart_2770155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770155 prefixEnd_2770155 := by exact prefixLift 2770155
  have htrace : WordTrace (prefixWord ++ tailWord_2770155) baseStart_2770155 baseEnd_2770155 := by
    simpa [prefixWord, tailWord_2770155, baseEnd_2770155] using wordTrace_append hprefix tailTrace_2770155
  have hstable : (prefixWord ++ tailWord_2770155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770155).length < 2 ^ (prefixWord ++ tailWord_2770155).sum := by decide
  have hdescent : baseEnd_2770155 < baseStart_2770155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770158 : List Nat := [4, 1, 2, 1, 1, 1, 2, 3, 8]
def baseStart_2770158 : Nat := 118140960795 + 2770158 * 2 ^ 59
def prefixEnd_2770158 : Nat := 4983230072969 + 3 ^ 40 * 2770158 * 2
def baseEnd_2770158 : Nat := 158046949210853108642809

theorem tailTrace_2770158 : CollatzResearch.WordTrace tailWord_2770158 prefixEnd_2770158 158046949210853108642809 := by
  unfold tailWord_2770158
  simp only [CollatzResearch.WordTrace]
  refine ⟨12629495337274768270708891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67357308465465430777114085 12629495337274768270708891)
  ·
    refine ⟨18944243005912152406063337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12629495337274768270708891 18944243005912152406063337)
    ·
      refine ⟨14208182254434114304547503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18944243005912152406063337 14208182254434114304547503)
      ·
        refine ⟨21312273381651171456821255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14208182254434114304547503 21312273381651171456821255)
        ·
          refine ⟨31968410072476757185231883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21312273381651171456821255 31968410072476757185231883)
          ·
            refine ⟨47952615108715135777847825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31968410072476757185231883 47952615108715135777847825)
            ·
              refine ⟨35964461331536351833385869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47952615108715135777847825 35964461331536351833385869)
              ·
                refine ⟨13486672999326131937519701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35964461331536351833385869 13486672999326131937519701)
                ·
                  refine ⟨158046949210853108642809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13486672999326131937519701 158046949210853108642809)
                  ·
                    rfl

theorem cell23_2770158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_2770158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770158 prefixEnd_2770158 := by exact prefixLift 2770158
  have htrace : WordTrace (prefixWord ++ tailWord_2770158) baseStart_2770158 baseEnd_2770158 := by
    simpa [prefixWord, tailWord_2770158, baseEnd_2770158] using wordTrace_append hprefix tailTrace_2770158
  have hstable : (prefixWord ++ tailWord_2770158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770158).length < 2 ^ (prefixWord ++ tailWord_2770158).sum := by decide
  have hdescent : baseEnd_2770158 < baseStart_2770158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770168 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 4, 5, 3]
def baseStart_2770168 : Nat := 118140960795 + 2770168 * 2 ^ 59
def prefixEnd_2770168 : Nat := 4983230072969 + 3 ^ 40 * 2770168 * 2
def baseEnd_2770168 : Nat := 1422427677704222938660235

theorem tailTrace_2770168 : CollatzResearch.WordTrace tailWord_2770168 prefixEnd_2770168 1422427677704222938660235 := by
  unfold tailWord_2770168
  simp only [CollatzResearch.WordTrace]
  refine ⟨50518163714080958936767579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67357551618774611915690105 50518163714080958936767579)
  ·
    refine ⟨75777245571121438405151369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50518163714080958936767579 75777245571121438405151369)
    ·
      refine ⟨56832934178341078803863527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75777245571121438405151369 56832934178341078803863527)
      ·
        refine ⟨85249401267511618205795291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56832934178341078803863527 85249401267511618205795291)
        ·
          refine ⟨127874101901267427308692937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85249401267511618205795291 127874101901267427308692937)
          ·
            refine ⟨95905576425950570481519703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127874101901267427308692937 95905576425950570481519703)
            ·
              refine ⟨143858364638925855722279555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95905576425950570481519703 143858364638925855722279555)
              ·
                refine ⟨215787546958388783583419333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143858364638925855722279555 215787546958388783583419333)
                ·
                  refine ⟨40460165054697896921891125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 215787546958388783583419333 40460165054697896921891125)
                  ·
                    refine ⟨3793140473877927836427293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40460165054697896921891125 3793140473877927836427293)
                    ·
                      refine ⟨1422427677704222938660235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3793140473877927836427293 1422427677704222938660235)
                      ·
                        rfl

theorem cell23_2770168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 5, 3].length) (baseStart_2770168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770168 prefixEnd_2770168 := by exact prefixLift 2770168
  have htrace : WordTrace (prefixWord ++ tailWord_2770168) baseStart_2770168 baseEnd_2770168 := by
    simpa [prefixWord, tailWord_2770168, baseEnd_2770168] using wordTrace_append hprefix tailTrace_2770168
  have hstable : (prefixWord ++ tailWord_2770168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770168).length < 2 ^ (prefixWord ++ tailWord_2770168).sum := by decide
  have hdescent : baseEnd_2770168 < baseStart_2770168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770212 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 4, 3, 2]
def baseStart_2770212 : Nat := 118140960795 + 2770212 * 2 ^ 59
def prefixEnd_2770212 : Nat := 4983230072969 + 3 ^ 40 * 2770212 * 2
def baseEnd_2770212 : Nat := 1422450270853020766510033

theorem tailTrace_2770212 : CollatzResearch.WordTrace tailWord_2770212 prefixEnd_2770212 1422450270853020766510033 := by
  unfold tailWord_2770212
  simp only [CollatzResearch.WordTrace]
  refine ⟨50518966120001256694068445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67358621493335008925424593 50518966120001256694068445)
  ·
    refine ⟨18944612295000471260275667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50518966120001256694068445 18944612295000471260275667)
    ·
      refine ⟨28416918442500706890413501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18944612295000471260275667 28416918442500706890413501)
      ·
        refine ⟨10656344415937765083905063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28416918442500706890413501 10656344415937765083905063)
        ·
          refine ⟨15984516623906647625857595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10656344415937765083905063 15984516623906647625857595)
          ·
            refine ⟨23976774935859971438786393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15984516623906647625857595 23976774935859971438786393)
            ·
              refine ⟨17982581201894978579089795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23976774935859971438786393 17982581201894978579089795)
              ·
                refine ⟨26973871802842467868634693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17982581201894978579089795 26973871802842467868634693)
                ·
                  refine ⟨5057600963032962725369005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26973871802842467868634693 5057600963032962725369005)
                  ·
                    refine ⟨1896600361137361022013377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5057600963032962725369005 1896600361137361022013377)
                    ·
                      refine ⟨1422450270853020766510033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1896600361137361022013377 1422450270853020766510033)
                      ·
                        rfl

theorem cell23_2770212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_2770212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770212 prefixEnd_2770212 := by exact prefixLift 2770212
  have htrace : WordTrace (prefixWord ++ tailWord_2770212) baseStart_2770212 baseEnd_2770212 := by
    simpa [prefixWord, tailWord_2770212, baseEnd_2770212] using wordTrace_append hprefix tailTrace_2770212
  have hstable : (prefixWord ++ tailWord_2770212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770212).length < 2 ^ (prefixWord ++ tailWord_2770212).sum := by decide
  have hdescent : baseEnd_2770212 < baseStart_2770212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770245 : List Nat := [1, 3, 1, 1, 1, 2, 1, 5, 3, 2, 3]
def baseStart_2770245 : Nat := 118140960795 + 2770245 * 2 ^ 59
def prefixEnd_2770245 : Nat := 4983230072969 + 3 ^ 40 * 2770245 * 2
def baseEnd_2770245 : Nat := 1422467215714619137397381

theorem tailTrace_2770245 : CollatzResearch.WordTrace tailWord_2770245 prefixEnd_2770245 1422467215714619137397381 := by
  unfold tailWord_2770245
  simp only [CollatzResearch.WordTrace]
  refine ⟨101039135848882960024088189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67359423899255306682725459 101039135848882960024088189)
  ·
    refine ⟨37889675943331110009033071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101039135848882960024088189 37889675943331110009033071)
    ·
      refine ⟨56834513914996665013549607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37889675943331110009033071 56834513914996665013549607)
      ·
        refine ⟨85251770872494997520324411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56834513914996665013549607 85251770872494997520324411)
        ·
          refine ⟨127877656308742496280486617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85251770872494997520324411 127877656308742496280486617)
          ·
            refine ⟨95908242231556872210364963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127877656308742496280486617 95908242231556872210364963)
            ·
              refine ⟨143862363347335308315547445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95908242231556872210364963 143862363347335308315547445)
              ·
                refine ⟨13487096563812685154582573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 143862363347335308315547445 13487096563812685154582573)
                ·
                  refine ⟨5057661211429756932968465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13487096563812685154582573 5057661211429756932968465)
                  ·
                    refine ⟨3793245908572317699726349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5057661211429756932968465 3793245908572317699726349)
                    ·
                      refine ⟨1422467215714619137397381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3793245908572317699726349 1422467215714619137397381)
                      ·
                        rfl

theorem cell23_2770245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 2, 3].length) (baseStart_2770245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770245 prefixEnd_2770245 := by exact prefixLift 2770245
  have htrace : WordTrace (prefixWord ++ tailWord_2770245) baseStart_2770245 baseEnd_2770245 := by
    simpa [prefixWord, tailWord_2770245, baseEnd_2770245] using wordTrace_append hprefix tailTrace_2770245
  have hstable : (prefixWord ++ tailWord_2770245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770245).length < 2 ^ (prefixWord ++ tailWord_2770245).sum := by decide
  have hdescent : baseEnd_2770245 < baseStart_2770245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770276 : List Nat := [2, 3, 1, 1, 3, 4, 1, 1, 3, 2, 2]
def baseStart_2770276 : Nat := 118140960795 + 2770276 * 2 ^ 59
def prefixEnd_2770276 : Nat := 4983230072969 + 3 ^ 40 * 2770276 * 2
def baseEnd_2770276 : Nat := 1422483133614908516109739

theorem tailTrace_2770276 : CollatzResearch.WordTrace tailWord_2770276 prefixEnd_2770276 1422483133614908516109739 := by
  unfold tailWord_2770276
  simp only [CollatzResearch.WordTrace]
  refine ⟨50520133255885326159233341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67360177674513768212311121 50520133255885326159233341)
  ·
    refine ⟨18945049970956997309712503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50520133255885326159233341 18945049970956997309712503)
    ·
      refine ⟨28417574956435495964568755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18945049970956997309712503 28417574956435495964568755)
      ·
        refine ⟨42626362434653243946853133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28417574956435495964568755 42626362434653243946853133)
        ·
          refine ⟨15984885912994966480069925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42626362434653243946853133 15984885912994966480069925)
          ·
            refine ⟨2997166108686556215013111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15984885912994966480069925 2997166108686556215013111)
            ·
              refine ⟨4495749163029834322519667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2997166108686556215013111 4495749163029834322519667)
              ·
                refine ⟨6743623744544751483779501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4495749163029834322519667 6743623744544751483779501)
                ·
                  refine ⟨2528858904204281806417313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6743623744544751483779501 2528858904204281806417313)
                  ·
                    refine ⟨1896644178153211354812985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2528858904204281806417313 1896644178153211354812985)
                    ·
                      refine ⟨1422483133614908516109739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1896644178153211354812985 1422483133614908516109739)
                      ·
                        rfl

theorem cell23_2770276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 3, 2, 2].length) (baseStart_2770276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770276 prefixEnd_2770276 := by exact prefixLift 2770276
  have htrace : WordTrace (prefixWord ++ tailWord_2770276) baseStart_2770276 baseEnd_2770276 := by
    simpa [prefixWord, tailWord_2770276, baseEnd_2770276] using wordTrace_append hprefix tailTrace_2770276
  have hstable : (prefixWord ++ tailWord_2770276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770276).length < 2 ^ (prefixWord ++ tailWord_2770276).sum := by decide
  have hdescent : baseEnd_2770276 < baseStart_2770276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770282 : List Nat := [3, 1, 3, 3, 2, 1, 2, 8]
def baseStart_2770282 : Nat := 118140960795 + 2770282 * 2 ^ 59
def prefixEnd_2770282 : Nat := 4983230072969 + 3 ^ 40 * 2770282 * 2
def baseEnd_2770282 : Nat := 52684674611067981208693

theorem tailTrace_2770282 : CollatzResearch.WordTrace tailWord_2770282 prefixEnd_2770282 52684674611067981208693 := by
  unfold tailWord_2770282
  simp only [CollatzResearch.WordTrace]
  refine ⟨25260121337437228835796275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67360323566499276895456733 25260121337437228835796275)
  ·
    refine ⟨37890182006155843253694413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25260121337437228835796275 37890182006155843253694413)
    ·
      refine ⟨14208818252308441220135405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37890182006155843253694413 14208818252308441220135405)
      ·
        refine ⟨5328306844615665457550777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14208818252308441220135405 5328306844615665457550777)
        ·
          refine ⟨3996230133461749093163083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5328306844615665457550777 3996230133461749093163083)
          ·
            refine ⟨5994345200192623639744625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3996230133461749093163083 5994345200192623639744625)
            ·
              refine ⟨4495758900144467729808469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5994345200192623639744625 4495758900144467729808469)
              ·
                refine ⟨52684674611067981208693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4495758900144467729808469 52684674611067981208693)
                ·
                  rfl

theorem cell23_2770282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 8].length) (baseStart_2770282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770282 prefixEnd_2770282 := by exact prefixLift 2770282
  have htrace : WordTrace (prefixWord ++ tailWord_2770282) baseStart_2770282 baseEnd_2770282 := by
    simpa [prefixWord, tailWord_2770282, baseEnd_2770282] using wordTrace_append hprefix tailTrace_2770282
  have hstable : (prefixWord ++ tailWord_2770282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770282).length < 2 ^ (prefixWord ++ tailWord_2770282).sum := by decide
  have hdescent : baseEnd_2770282 < baseStart_2770282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770286 : List Nat := [4, 1, 2, 4, 1, 1, 1, 3, 2, 4]
def baseStart_2770286 : Nat := 118140960795 + 2770286 * 2 ^ 59
def prefixEnd_2770286 : Nat := 4983230072969 + 3 ^ 40 * 2770286 * 2
def baseEnd_2770286 : Nat := 474162756140484492328231

theorem tailTrace_2770286 : CollatzResearch.WordTrace tailWord_2770286 prefixEnd_2770286 474162756140484492328231 := by
  unfold tailWord_2770286
  simp only [CollatzResearch.WordTrace]
  refine ⟨12630078905216803003291339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67360420827822949350887141 12630078905216803003291339)
  ·
    refine ⟨18945118357825204504937009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12630078905216803003291339 18945118357825204504937009)
    ·
      refine ⟨14208838768368903378702757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18945118357825204504937009 14208838768368903378702757)
      ·
        refine ⟨2664157269069169383506767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14208838768368903378702757 2664157269069169383506767)
        ·
          refine ⟨3996235903603754075260151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2664157269069169383506767 3996235903603754075260151)
          ·
            refine ⟨5994353855405631112890227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3996235903603754075260151 5994353855405631112890227)
            ·
              refine ⟨8991530783108446669335341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5994353855405631112890227 8991530783108446669335341)
              ·
                refine ⟨3371824043665667501000753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8991530783108446669335341 3371824043665667501000753)
                ·
                  refine ⟨2528868032749250625750565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3371824043665667501000753 2528868032749250625750565)
                  ·
                    refine ⟨474162756140484492328231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2528868032749250625750565 474162756140484492328231)
                    ·
                      rfl

theorem cell23_2770286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_2770286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770286 prefixEnd_2770286 := by exact prefixLift 2770286
  have htrace : WordTrace (prefixWord ++ tailWord_2770286) baseStart_2770286 baseEnd_2770286 := by
    simpa [prefixWord, tailWord_2770286, baseEnd_2770286] using wordTrace_append hprefix tailTrace_2770286
  have hstable : (prefixWord ++ tailWord_2770286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770286).length < 2 ^ (prefixWord ++ tailWord_2770286).sum := by decide
  have hdescent : baseEnd_2770286 < baseStart_2770286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770382 : List Nat := [4, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3]
def baseStart_2770382 : Nat := 118140960795 + 2770382 * 2 ^ 59
def prefixEnd_2770382 : Nat := 4983230072969 + 3 ^ 40 * 2770382 * 2
def baseEnd_2770382 : Nat := 1422537562564285101384251

theorem tailTrace_2770382 : CollatzResearch.WordTrace tailWord_2770382 prefixEnd_2770382 1422537562564285101384251 := by
  unfold tailWord_2770382
  simp only [CollatzResearch.WordTrace]
  refine ⟨12630516581173329052728175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67362755099591088281216933 12630516581173329052728175)
  ·
    refine ⟨18945774871759993579092263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12630516581173329052728175 18945774871759993579092263)
    ·
      refine ⟨28418662307639990368638395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18945774871759993579092263 28418662307639990368638395)
      ·
        refine ⟨42627993461459985552957593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28418662307639990368638395 42627993461459985552957593)
        ·
          refine ⟨31970995096094989164718195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42627993461459985552957593 31970995096094989164718195)
          ·
            refine ⟨47956492644142483747077293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31970995096094989164718195 47956492644142483747077293)
            ·
              refine ⟨17983684741553431405153985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47956492644142483747077293 17983684741553431405153985)
              ·
                refine ⟨13487763556165073553865489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17983684741553431405153985 13487763556165073553865489)
                ·
                  refine ⟨10115822667123805165399117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13487763556165073553865489 10115822667123805165399117)
                  ·
                    refine ⟨3793433500171426937024669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10115822667123805165399117 3793433500171426937024669)
                    ·
                      refine ⟨1422537562564285101384251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3793433500171426937024669 1422537562564285101384251)
                      ·
                        rfl

theorem cell23_2770382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_2770382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770382 prefixEnd_2770382 := by exact prefixLift 2770382
  have htrace : WordTrace (prefixWord ++ tailWord_2770382) baseStart_2770382 baseEnd_2770382 := by
    simpa [prefixWord, tailWord_2770382, baseEnd_2770382] using wordTrace_append hprefix tailTrace_2770382
  have hstable : (prefixWord ++ tailWord_2770382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770382).length < 2 ^ (prefixWord ++ tailWord_2770382).sum := by decide
  have hdescent : baseEnd_2770382 < baseStart_2770382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770392 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 1, 7, 2]
def baseStart_2770392 : Nat := 118140960795 + 2770392 * 2 ^ 59
def prefixEnd_2770392 : Nat := 4983230072969 + 3 ^ 40 * 2770392 * 2
def baseEnd_2770392 : Nat := 1422542697370830062259205

theorem tailTrace_2770392 : CollatzResearch.WordTrace tailWord_2770392 prefixEnd_2770392 1422542697370830062259205 := by
  unfold tailWord_2770392
  simp only [CollatzResearch.WordTrace]
  refine ⟨50522248689675202064844715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67362998252900269419792953 50522248689675202064844715)
  ·
    refine ⟨75783373034512803097267073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50522248689675202064844715 75783373034512803097267073)
    ·
      refine ⟨56837529775884602322950305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75783373034512803097267073 56837529775884602322950305)
      ·
        refine ⟨42628147331913451742212729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56837529775884602322950305 42628147331913451742212729)
        ·
          refine ⟨31971110498935088806659547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42628147331913451742212729 31971110498935088806659547)
          ·
            refine ⟨47956665748402633209989321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31971110498935088806659547 47956665748402633209989321)
            ·
              refine ⟨35967499311301974907491991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47956665748402633209989321 35967499311301974907491991)
              ·
                refine ⟨53951248966952962361237987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35967499311301974907491991 53951248966952962361237987)
                ·
                  refine ⟨80926873450429443541856981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53951248966952962361237987 80926873450429443541856981)
                  ·
                    refine ⟨1896723596494440083012273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 80926873450429443541856981 1896723596494440083012273)
                    ·
                      refine ⟨1422542697370830062259205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1896723596494440083012273 1422542697370830062259205)
                      ·
                        rfl

theorem cell23_2770392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 7, 2].length) (baseStart_2770392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770392 prefixEnd_2770392 := by exact prefixLift 2770392
  have htrace : WordTrace (prefixWord ++ tailWord_2770392) baseStart_2770392 baseEnd_2770392 := by
    simpa [prefixWord, tailWord_2770392, baseEnd_2770392] using wordTrace_append hprefix tailTrace_2770392
  have hstable : (prefixWord ++ tailWord_2770392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770392).length < 2 ^ (prefixWord ++ tailWord_2770392).sum := by decide
  have hdescent : baseEnd_2770392 < baseStart_2770392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770425 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 2, 3, 5]
def baseStart_2770425 : Nat := 118140960795 + 2770425 * 2 ^ 59
def prefixEnd_2770425 : Nat := 4983230072969 + 3 ^ 40 * 2770425 * 2
def baseEnd_2770425 : Nat := 1422559642232428433146553

theorem tailTrace_2770425 : CollatzResearch.WordTrace tailWord_2770425 prefixEnd_2770425 1422559642232428433146553 := by
  unfold tailWord_2770425
  simp only [CollatzResearch.WordTrace]
  refine ⟨101045700988230850765640729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67363800658820567177093819 101045700988230850765640729)
  ·
    refine ⟨75784275741173138074230547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101045700988230850765640729 75784275741173138074230547)
    ·
      refine ⟨113676413611759707111345821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75784275741173138074230547 113676413611759707111345821)
      ·
        refine ⟨42628655104409890166754683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113676413611759707111345821 42628655104409890166754683)
        ·
          refine ⟨63942982656614835250132025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42628655104409890166754683 63942982656614835250132025)
          ·
            refine ⟨47957236992461126437599019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63942982656614835250132025 47957236992461126437599019)
            ·
              refine ⟨71935855488691689656398529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47957236992461126437599019 71935855488691689656398529)
              ·
                refine ⟨53951891616518767242298897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71935855488691689656398529 53951891616518767242298897)
                ·
                  refine ⟨40463918712389075431724173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53951891616518767242298897 40463918712389075431724173)
                  ·
                    refine ⟨15173969517145903286896565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40463918712389075431724173 15173969517145903286896565)
                    ·
                      refine ⟨1422559642232428433146553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15173969517145903286896565 1422559642232428433146553)
                      ·
                        rfl

theorem cell23_2770425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_2770425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770425 prefixEnd_2770425 := by exact prefixLift 2770425
  have htrace : WordTrace (prefixWord ++ tailWord_2770425) baseStart_2770425 baseEnd_2770425 := by
    simpa [prefixWord, tailWord_2770425, baseEnd_2770425] using wordTrace_append hprefix tailTrace_2770425
  have hstable : (prefixWord ++ tailWord_2770425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770425).length < 2 ^ (prefixWord ++ tailWord_2770425).sum := by decide
  have hdescent : baseEnd_2770425 < baseStart_2770425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770435 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 6]
def baseStart_2770435 : Nat := 118140960795 + 2770435 * 2 ^ 59
def prefixEnd_2770435 : Nat := 4983230072969 + 3 ^ 40 * 2770435 * 2
def baseEnd_2770435 : Nat := 1422564777038973394021507

theorem tailTrace_2770435 : CollatzResearch.WordTrace tailWord_2770435 prefixEnd_2770435 1422564777038973394021507 := by
  unfold tailWord_2770435
  simp only [CollatzResearch.WordTrace]
  refine ⟨101046065718194622473504759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67364043812129748315669839 101046065718194622473504759)
  ·
    refine ⟨151569098577291933710257139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101046065718194622473504759 151569098577291933710257139)
    ·
      refine ⟨227353647865937900565385709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151569098577291933710257139 227353647865937900565385709)
      ·
        refine ⟨85257617949726712712019641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227353647865937900565385709 85257617949726712712019641)
        ·
          refine ⟨63943213462295034534014731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85257617949726712712019641 63943213462295034534014731)
          ·
            refine ⟨95914820193442551801022097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63943213462295034534014731 95914820193442551801022097)
            ·
              refine ⟨71936115145081913850766573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95914820193442551801022097 71936115145081913850766573)
              ·
                refine ⟨26976043179405717694037465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71936115145081913850766573 26976043179405717694037465)
                ·
                  refine ⟨20232032384554288270528099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26976043179405717694037465 20232032384554288270528099)
                  ·
                    refine ⟨30348048576831432405792149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20232032384554288270528099 30348048576831432405792149)
                    ·
                      refine ⟨1422564777038973394021507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30348048576831432405792149 1422564777038973394021507)
                      ·
                        rfl

theorem cell23_2770435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_2770435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770435 prefixEnd_2770435 := by exact prefixLift 2770435
  have htrace : WordTrace (prefixWord ++ tailWord_2770435) baseStart_2770435 baseEnd_2770435 := by
    simpa [prefixWord, tailWord_2770435, baseEnd_2770435] using wordTrace_append hprefix tailTrace_2770435
  have hstable : (prefixWord ++ tailWord_2770435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770435).length < 2 ^ (prefixWord ++ tailWord_2770435).sum := by decide
  have hdescent : baseEnd_2770435 < baseStart_2770435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770439 : List Nat := [1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 4]
def baseStart_2770439 : Nat := 118140960795 + 2770439 * 2 ^ 59
def prefixEnd_2770439 : Nat := 4983230072969 + 3 ^ 40 * 2770439 * 2
def baseEnd_2770439 : Nat := 1422566830961591378371489

theorem tailTrace_2770439 : CollatzResearch.WordTrace tailWord_2770439 prefixEnd_2770439 1422566830961591378371489 := by
  unfold tailWord_2770439
  simp only [CollatzResearch.WordTrace]
  refine ⟨101046211610180131156650371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67364141073453420771100247 101046211610180131156650371)
  ·
    refine ⟨151569317415270196734975557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101046211610180131156650371 151569317415270196734975557)
    ·
      refine ⟨28419247015363161887807917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151569317415270196734975557 28419247015363161887807917)
      ·
        refine ⟨10657217630761185707927969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28419247015363161887807917 10657217630761185707927969)
        ·
          refine ⟨7992913223070889280945977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10657217630761185707927969 7992913223070889280945977)
          ·
            refine ⟨5994684917303166960709483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7992913223070889280945977 5994684917303166960709483)
            ·
              refine ⟨8992027375954750441064225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5994684917303166960709483 8992027375954750441064225)
              ·
                refine ⟨6744020531966062830798169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8992027375954750441064225 6744020531966062830798169)
                ·
                  refine ⟨5058015398974547123098627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6744020531966062830798169 5058015398974547123098627)
                  ·
                    refine ⟨7587023098461820684647941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5058015398974547123098627 7587023098461820684647941)
                    ·
                      refine ⟨1422566830961591378371489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7587023098461820684647941 1422566830961591378371489)
                      ·
                        rfl

theorem cell23_2770439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_2770439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770439 prefixEnd_2770439 := by exact prefixLift 2770439
  have htrace : WordTrace (prefixWord ++ tailWord_2770439) baseStart_2770439 baseEnd_2770439 := by
    simpa [prefixWord, tailWord_2770439, baseEnd_2770439] using wordTrace_append hprefix tailTrace_2770439
  have hstable : (prefixWord ++ tailWord_2770439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770439).length < 2 ^ (prefixWord ++ tailWord_2770439).sum := by decide
  have hdescent : baseEnd_2770439 < baseStart_2770439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770512 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 4]
def baseStart_2770512 : Nat := 118140960795 + 2770512 * 2 ^ 59
def prefixEnd_2770512 : Nat := 4983230072969 + 3 ^ 40 * 2770512 * 2
def baseEnd_2770512 : Nat := 1422604315049369592758653

theorem tailTrace_2770512 : CollatzResearch.WordTrace tailWord_2770512 prefixEnd_2770512 1422604315049369592758653 := by
  unfold tailWord_2770512
  simp only [CollatzResearch.WordTrace]
  refine ⟨50524437069457832312028895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67365916092610443082705193 50524437069457832312028895)
  ·
    refine ⟨75786655604186748468043343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50524437069457832312028895 75786655604186748468043343)
    ·
      refine ⟨113679983406280122702065015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75786655604186748468043343 113679983406280122702065015)
      ·
        refine ⟨170519975109420184053097523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113679983406280122702065015 170519975109420184053097523)
        ·
          refine ⟨255779962664130276079646285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170519975109420184053097523 255779962664130276079646285)
          ·
            refine ⟨95917485999048853529867357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255779962664130276079646285 95917485999048853529867357)
            ·
              refine ⟨35969057249643320073700259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95917485999048853529867357 35969057249643320073700259)
              ·
                refine ⟨53953585874464980110550389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35969057249643320073700259 53953585874464980110550389)
                ·
                  refine ⟨5058148675731091885364099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53953585874464980110550389 5058148675731091885364099)
                  ·
                    refine ⟨7587223013596637828046149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5058148675731091885364099 7587223013596637828046149)
                    ·
                      refine ⟨1422604315049369592758653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7587223013596637828046149 1422604315049369592758653)
                      ·
                        rfl

theorem cell23_2770512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 4].length) (baseStart_2770512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770512 prefixEnd_2770512 := by exact prefixLift 2770512
  have htrace : WordTrace (prefixWord ++ tailWord_2770512) baseStart_2770512 baseEnd_2770512 := by
    simpa [prefixWord, tailWord_2770512, baseEnd_2770512] using wordTrace_append hprefix tailTrace_2770512
  have hstable : (prefixWord ++ tailWord_2770512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770512).length < 2 ^ (prefixWord ++ tailWord_2770512).sum := by decide
  have hdescent : baseEnd_2770512 < baseStart_2770512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770529 : List Nat := [1, 2, 3, 1, 1, 3, 2, 4, 1, 1, 4]
def baseStart_2770529 : Nat := 118140960795 + 2770529 * 2 ^ 59
def prefixEnd_2770529 : Nat := 4983230072969 + 3 ^ 40 * 2770529 * 2
def baseEnd_2770529 : Nat := 1422613044220496026246075

theorem tailTrace_2770529 : CollatzResearch.WordTrace tailWord_2770529 prefixEnd_2770529 1422613044220496026246075 := by
  unfold tailWord_2770529
  simp only [CollatzResearch.WordTrace]
  refine ⟨101049494179854076527426641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67366329453236051018284427 101049494179854076527426641)
  ·
    refine ⟨75787120634890557395569981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101049494179854076527426641 75787120634890557395569981)
    ·
      refine ⟨28420170238083959023338743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75787120634890557395569981 28420170238083959023338743)
      ·
        refine ⟨42630255357125938535008115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28420170238083959023338743 42630255357125938535008115)
        ·
          refine ⟨63945383035688907802512173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42630255357125938535008115 63945383035688907802512173)
          ·
            refine ⟨23979518638383340425942065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63945383035688907802512173 23979518638383340425942065)
            ·
              refine ⟨17984638978787505319456549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23979518638383340425942065 17984638978787505319456549)
              ·
                refine ⟨3372119808522657247398103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17984638978787505319456549 3372119808522657247398103)
                ·
                  refine ⟨5058179712783985871097155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3372119808522657247398103 5058179712783985871097155)
                  ·
                    refine ⟨7587269569175978806645733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5058179712783985871097155 7587269569175978806645733)
                    ·
                      refine ⟨1422613044220496026246075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7587269569175978806645733 1422613044220496026246075)
                      ·
                        rfl

theorem cell23_2770529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_2770529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770529 prefixEnd_2770529 := by exact prefixLift 2770529
  have htrace : WordTrace (prefixWord ++ tailWord_2770529) baseStart_2770529 baseEnd_2770529 := by
    simpa [prefixWord, tailWord_2770529, baseEnd_2770529] using wordTrace_append hprefix tailTrace_2770529
  have hstable : (prefixWord ++ tailWord_2770529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770529).length < 2 ^ (prefixWord ++ tailWord_2770529).sum := by decide
  have hdescent : baseEnd_2770529 < baseStart_2770529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770533 : List Nat := [1, 3, 1, 3, 3, 3, 1, 1, 2, 3, 2]
def baseStart_2770533 : Nat := 118140960795 + 2770533 * 2 ^ 59
def prefixEnd_2770533 : Nat := 4983230072969 + 3 ^ 40 * 2770533 * 2
def baseEnd_2770533 : Nat := 1422615098143114010596057

theorem tailTrace_2770533 : CollatzResearch.WordTrace tailWord_2770533 prefixEnd_2770533 1422615098143114010596057 := by
  unfold tailWord_2770533
  simp only [CollatzResearch.WordTrace]
  refine ⟨101049640071839585210572253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67366426714559723473714835 101049640071839585210572253)
  ·
    refine ⟨37893615026939844453964595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101049640071839585210572253 37893615026939844453964595)
    ·
      refine ⟨56840422540409766680946893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37893615026939844453964595 56840422540409766680946893)
      ·
        refine ⟨21315158452653662505355085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56840422540409766680946893 21315158452653662505355085)
        ·
          refine ⟨7993184419745123439508157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21315158452653662505355085 7993184419745123439508157)
          ·
            refine ⟨2997444157404421289815559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7993184419745123439508157 2997444157404421289815559)
            ·
              refine ⟨4496166236106631934723339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2997444157404421289815559 4496166236106631934723339)
              ·
                refine ⟨6744249354159947902085009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4496166236106631934723339 6744249354159947902085009)
                ·
                  refine ⟨5058187015619960926563757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6744249354159947902085009 5058187015619960926563757)
                  ·
                    refine ⟨1896820130857485347461409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5058187015619960926563757 1896820130857485347461409)
                    ·
                      refine ⟨1422615098143114010596057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1896820130857485347461409 1422615098143114010596057)
                      ·
                        rfl

theorem cell23_2770533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_2770533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770533 prefixEnd_2770533 := by exact prefixLift 2770533
  have htrace : WordTrace (prefixWord ++ tailWord_2770533) baseStart_2770533 baseEnd_2770533 := by
    simpa [prefixWord, tailWord_2770533, baseEnd_2770533] using wordTrace_append hprefix tailTrace_2770533
  have hstable : (prefixWord ++ tailWord_2770533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770533).length < 2 ^ (prefixWord ++ tailWord_2770533).sum := by decide
  have hdescent : baseEnd_2770533 < baseStart_2770533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770546 : List Nat := [3, 2, 1, 2, 3, 2, 1, 3, 1, 1, 4]
def baseStart_2770546 : Nat := 118140960795 + 2770546 * 2 ^ 59
def prefixEnd_2770546 : Nat := 4983230072969 + 3 ^ 40 * 2770546 * 2
def baseEnd_2770546 : Nat := 1422621773391622459733497

theorem tailTrace_2770546 : CollatzResearch.WordTrace tailWord_2770546 prefixEnd_2770546 1422621773391622459733497 := by
  unfold tailWord_2770546
  simp only [CollatzResearch.WordTrace]
  refine ⟨25262528555198122107698873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67366742813861658953863661 25262528555198122107698873)
  ·
    refine ⟨18946896416398591580774155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25262528555198122107698873 18946896416398591580774155)
    ·
      refine ⟨28420344624597887371161233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18946896416398591580774155 28420344624597887371161233)
      ·
        refine ⟨21315258468448415528370925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28420344624597887371161233 21315258468448415528370925)
        ·
          refine ⟨7993221925668155823139097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21315258468448415528370925 7993221925668155823139097)
          ·
            refine ⟨5994916444251116867354323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7993221925668155823139097 5994916444251116867354323)
            ·
              refine ⟨8992374666376675301031485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5994916444251116867354323 8992374666376675301031485)
              ·
                refine ⟨3372140499891253237886807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8992374666376675301031485 3372140499891253237886807)
                ·
                  refine ⟨5058210749836879856830211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3372140499891253237886807 5058210749836879856830211)
                  ·
                    refine ⟨7587316124755319785245317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5058210749836879856830211 7587316124755319785245317)
                    ·
                      refine ⟨1422621773391622459733497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7587316124755319785245317 1422621773391622459733497)
                      ·
                        rfl

theorem cell23_2770546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_2770546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770546 prefixEnd_2770546 := by exact prefixLift 2770546
  have htrace : WordTrace (prefixWord ++ tailWord_2770546) baseStart_2770546 baseEnd_2770546 := by
    simpa [prefixWord, tailWord_2770546, baseEnd_2770546] using wordTrace_append hprefix tailTrace_2770546
  have hstable : (prefixWord ++ tailWord_2770546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770546).length < 2 ^ (prefixWord ++ tailWord_2770546).sum := by decide
  have hdescent : baseEnd_2770546 < baseStart_2770546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770579 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 8, 1, 3]
def baseStart_2770579 : Nat := 118140960795 + 2770579 * 2 ^ 59
def prefixEnd_2770579 : Nat := 4983230072969 + 3 ^ 40 * 2770579 * 2
def baseEnd_2770579 : Nat := 1422638718253220830620845

theorem tailTrace_2770579 : CollatzResearch.WordTrace tailWord_2770579 prefixEnd_2770579 1422638718253220830620845 := by
  unfold tailWord_2770579
  simp only [CollatzResearch.WordTrace]
  refine ⟨101051317829672935066746791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67367545219781956711164527 101051317829672935066746791)
  ·
    refine ⟨151576976744509402600120187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101051317829672935066746791 151576976744509402600120187)
    ·
      refine ⟨227365465116764103900180281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151576976744509402600120187 227365465116764103900180281)
      ·
        refine ⟨170524098837573077925135211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227365465116764103900180281 170524098837573077925135211)
        ·
          refine ⟨255786148256359616887702817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170524098837573077925135211 255786148256359616887702817)
          ·
            refine ⟨191839611192269712665777113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255786148256359616887702817 191839611192269712665777113)
            ·
              refine ⟨143879708394202284499332835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191839611192269712665777113 143879708394202284499332835)
              ·
                refine ⟨215819562591303426748999253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143879708394202284499332835 215819562591303426748999253)
                ·
                  refine ⟨2529135499116837032214835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 215819562591303426748999253 2529135499116837032214835)
                  ·
                    refine ⟨3793703248675255548322253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2529135499116837032214835 3793703248675255548322253)
                    ·
                      refine ⟨1422638718253220830620845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3793703248675255548322253 1422638718253220830620845)
                      ·
                        rfl

theorem cell23_2770579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8, 1, 3].length) (baseStart_2770579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770579 prefixEnd_2770579 := by exact prefixLift 2770579
  have htrace : WordTrace (prefixWord ++ tailWord_2770579) baseStart_2770579 baseEnd_2770579 := by
    simpa [prefixWord, tailWord_2770579, baseEnd_2770579] using wordTrace_append hprefix tailTrace_2770579
  have hstable : (prefixWord ++ tailWord_2770579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770579).length < 2 ^ (prefixWord ++ tailWord_2770579).sum := by decide
  have hdescent : baseEnd_2770579 < baseStart_2770579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770596 : List Nat := [2, 3, 1, 2, 2, 2, 1, 2, 4, 1, 3]
def baseStart_2770596 : Nat := 118140960795 + 2770596 * 2 ^ 59
def prefixEnd_2770596 : Nat := 4983230072969 + 3 ^ 40 * 2770596 * 2
def baseEnd_2770596 : Nat := 1422647447424347264108267

theorem tailTrace_2770596 : CollatzResearch.WordTrace tailWord_2770596 prefixEnd_2770596 1422647447424347264108267 := by
  unfold tailWord_2770596
  simp only [CollatzResearch.WordTrace]
  refine ⟨50525968935305673485057821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67367958580407564646743761 50525968935305673485057821)
  ·
    refine ⟨18947238350739627556896683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50525968935305673485057821 18947238350739627556896683)
    ·
      refine ⟨28420857526109441335345025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18947238350739627556896683 28420857526109441335345025)
      ·
        refine ⟨21315643144582081001508769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28420857526109441335345025 21315643144582081001508769)
        ·
          refine ⟨15986732358436560751131577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21315643144582081001508769 15986732358436560751131577)
          ·
            refine ⟨11990049268827420563348683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15986732358436560751131577 11990049268827420563348683)
            ·
              refine ⟨17985073903241130845023025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11990049268827420563348683 17985073903241130845023025)
              ·
                refine ⟨13488805427430848133767269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17985073903241130845023025 13488805427430848133767269)
                ·
                  refine ⟨2529151017643284025081363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13488805427430848133767269 2529151017643284025081363)
                  ·
                    refine ⟨3793726526464926037622045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2529151017643284025081363 3793726526464926037622045)
                    ·
                      refine ⟨1422647447424347264108267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3793726526464926037622045 1422647447424347264108267)
                      ·
                        rfl

theorem cell23_2770596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_2770596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770596 prefixEnd_2770596 := by exact prefixLift 2770596
  have htrace : WordTrace (prefixWord ++ tailWord_2770596) baseStart_2770596 baseEnd_2770596 := by
    simpa [prefixWord, tailWord_2770596, baseEnd_2770596] using wordTrace_append hprefix tailTrace_2770596
  have hstable : (prefixWord ++ tailWord_2770596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770596).length < 2 ^ (prefixWord ++ tailWord_2770596).sum := by decide
  have hdescent : baseEnd_2770596 < baseStart_2770596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770600 : List Nat := [2, 1, 7, 1, 1, 1, 2, 1, 1, 1, 5]
def baseStart_2770600 : Nat := 118140960795 + 2770600 * 2 ^ 59
def prefixEnd_2770600 : Nat := 4983230072969 + 3 ^ 40 * 2770600 * 2
def baseEnd_2770600 : Nat := 1422649501346965248458249

theorem tailTrace_2770600 : CollatzResearch.WordTrace tailWord_2770600 prefixEnd_2770600 1422649501346965248458249 := by
  unfold tailWord_2770600
  simp only [CollatzResearch.WordTrace]
  refine ⟨50526041881298427826630627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67368055841731237102174169 50526041881298427826630627)
  ·
    refine ⟨75789062821947641739945941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50526041881298427826630627 75789062821947641739945941)
    ·
      refine ⟨1776306159889397853279983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 75789062821947641739945941 1776306159889397853279983)
      ·
        refine ⟨2664459239834096779919975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1776306159889397853279983 2664459239834096779919975)
        ·
          refine ⟨3996688859751145169879963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2664459239834096779919975 3996688859751145169879963)
          ·
            refine ⟨5995033289626717754819945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3996688859751145169879963 5995033289626717754819945)
            ·
              refine ⟨4496274967220038316114959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5995033289626717754819945 4496274967220038316114959)
              ·
                refine ⟨6744412450830057474172439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4496274967220038316114959 6744412450830057474172439)
                ·
                  refine ⟨10116618676245086211258659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6744412450830057474172439 10116618676245086211258659)
                  ·
                    refine ⟨15174928014367629316887989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10116618676245086211258659 15174928014367629316887989)
                    ·
                      refine ⟨1422649501346965248458249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15174928014367629316887989 1422649501346965248458249)
                      ·
                        rfl

theorem cell23_2770600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_2770600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770600 prefixEnd_2770600 := by exact prefixLift 2770600
  have htrace : WordTrace (prefixWord ++ tailWord_2770600) baseStart_2770600 baseEnd_2770600 := by
    simpa [prefixWord, tailWord_2770600, baseEnd_2770600] using wordTrace_append hprefix tailTrace_2770600
  have hstable : (prefixWord ++ tailWord_2770600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770600).length < 2 ^ (prefixWord ++ tailWord_2770600).sum := by decide
  have hdescent : baseEnd_2770600 < baseStart_2770600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770670 : List Nat := [4, 1, 2, 1, 1, 2, 4, 2, 2, 2, 2]
def baseStart_2770670 : Nat := 118140960795 + 2770670 * 2 ^ 59
def prefixEnd_2770670 : Nat := 4983230072969 + 3 ^ 40 * 2770670 * 2
def baseEnd_2770670 : Nat := 1422685444992779974582927

theorem tailTrace_2770670 : CollatzResearch.WordTrace tailWord_2770670 prefixEnd_2770670 1422685444992779974582927 := by
  unfold tailWord_2770670
  simp only [CollatzResearch.WordTrace]
  refine ⟨12631829609042907201038683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67369757914895505072206309 12631829609042907201038683)
  ·
    refine ⟨18947744413564360801558025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12631829609042907201038683 18947744413564360801558025)
    ·
      refine ⟨14210808310173270601168519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18947744413564360801558025 14210808310173270601168519)
      ·
        refine ⟨21316212465259905901752779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14210808310173270601168519 21316212465259905901752779)
        ·
          refine ⟨31974318697889858852629169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21316212465259905901752779 31974318697889858852629169)
          ·
            refine ⟨23980739023417394139471877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31974318697889858852629169 23980739023417394139471877)
            ·
              refine ⟨4496388566890761401150977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23980739023417394139471877 4496388566890761401150977)
              ·
                refine ⟨3372291425168071050863233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4496388566890761401150977 3372291425168071050863233)
                ·
                  refine ⟨2529218568876053288147425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3372291425168071050863233 2529218568876053288147425)
                  ·
                    refine ⟨1896913926657039966110569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2529218568876053288147425 1896913926657039966110569)
                    ·
                      refine ⟨1422685444992779974582927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1896913926657039966110569 1422685444992779974582927)
                      ·
                        rfl

theorem cell23_2770670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_2770670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770670 prefixEnd_2770670 := by exact prefixLift 2770670
  have htrace : WordTrace (prefixWord ++ tailWord_2770670) baseStart_2770670 baseEnd_2770670 := by
    simpa [prefixWord, tailWord_2770670, baseEnd_2770670] using wordTrace_append hprefix tailTrace_2770670
  have hstable : (prefixWord ++ tailWord_2770670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770670).length < 2 ^ (prefixWord ++ tailWord_2770670).sum := by decide
  have hdescent : baseEnd_2770670 < baseStart_2770670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770689 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 4, 5]
def baseStart_2770689 : Nat := 118140960795 + 2770689 * 2 ^ 59
def prefixEnd_2770689 : Nat := 4983230072969 + 3 ^ 40 * 2770689 * 2
def baseEnd_2770689 : Nat := 474231733708405133415113

theorem tailTrace_2770689 : CollatzResearch.WordTrace tailWord_2770689 prefixEnd_2770689 474231733708405133415113 := by
  unfold tailWord_2770689
  simp only [CollatzResearch.WordTrace]
  refine ⟨101055329859274423853251121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67370219906182949235500747 101055329859274423853251121)
  ·
    refine ⟨75791497394455817889938341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101055329859274423853251121 75791497394455817889938341)
    ·
      refine ⟨14210905761460465854363439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75791497394455817889938341 14210905761460465854363439)
      ·
        refine ⟨21316358642190698781545159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14210905761460465854363439 21316358642190698781545159)
        ·
          refine ⟨31974537963286048172317739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21316358642190698781545159 31974537963286048172317739)
          ·
            refine ⟨47961806944929072258476609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31974537963286048172317739 47961806944929072258476609)
            ·
              refine ⟨35971355208696804193857457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47961806944929072258476609 35971355208696804193857457)
              ·
                refine ⟨26978516406522603145393093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35971355208696804193857457 26978516406522603145393093)
                ·
                  refine ⟨5058471826222988089761205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26978516406522603145393093 5058471826222988089761205)
                  ·
                    refine ⟨474231733708405133415113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5058471826222988089761205 474231733708405133415113)
                    ·
                      rfl

theorem cell23_2770689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_2770689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770689 prefixEnd_2770689 := by exact prefixLift 2770689
  have htrace : WordTrace (prefixWord ++ tailWord_2770689) baseStart_2770689 baseEnd_2770689 := by
    simpa [prefixWord, tailWord_2770689, baseEnd_2770689] using wordTrace_append hprefix tailTrace_2770689
  have hstable : (prefixWord ++ tailWord_2770689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770689).length < 2 ^ (prefixWord ++ tailWord_2770689).sum := by decide
  have hdescent : baseEnd_2770689 < baseStart_2770689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770696 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 2, 5, 2]
def baseStart_2770696 : Nat := 118140960795 + 2770696 * 2 ^ 59
def prefixEnd_2770696 : Nat := 4983230072969 + 3 ^ 40 * 2770696 * 2
def baseEnd_2770696 : Nat := 1422698795489796872857807

theorem tailTrace_2770696 : CollatzResearch.WordTrace tailWord_2770696 prefixEnd_2770696 1422698795489796872857807 := by
  unfold tailWord_2770696
  simp only [CollatzResearch.WordTrace]
  refine ⟨50527792585124532024377971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67370390113499376032503961 50527792585124532024377971)
  ·
    refine ⟨75791688877686798036566957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50527792585124532024377971 75791688877686798036566957)
    ·
      refine ⟨28421883329132549263712609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75791688877686798036566957 28421883329132549263712609)
      ·
        refine ⟨21316412496849411947784457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28421883329132549263712609 21316412496849411947784457)
        ·
          refine ⟨15987309372637058960838343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21316412496849411947784457 15987309372637058960838343)
          ·
            refine ⟨23980964058955588441257515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15987309372637058960838343 23980964058955588441257515)
            ·
              refine ⟨35971446088433382661886273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23980964058955588441257515 35971446088433382661886273)
              ·
                refine ⟨26978584566325036996414705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35971446088433382661886273 26978584566325036996414705)
                ·
                  refine ⟨20233938424743777747311029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26978584566325036996414705 20233938424743777747311029)
                  ·
                    refine ⟨1896931727319729163810409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20233938424743777747311029 1896931727319729163810409)
                    ·
                      refine ⟨1422698795489796872857807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1896931727319729163810409 1422698795489796872857807)
                      ·
                        rfl

theorem cell23_2770696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_2770696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770696 prefixEnd_2770696 := by exact prefixLift 2770696
  have htrace : WordTrace (prefixWord ++ tailWord_2770696) baseStart_2770696 baseEnd_2770696 := by
    simpa [prefixWord, tailWord_2770696, baseEnd_2770696] using wordTrace_append hprefix tailTrace_2770696
  have hstable : (prefixWord ++ tailWord_2770696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770696).length < 2 ^ (prefixWord ++ tailWord_2770696).sum := by decide
  have hdescent : baseEnd_2770696 < baseStart_2770696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770708 : List Nat := [2, 4, 4, 1, 2, 1, 2, 1, 1, 3, 2]
def baseStart_2770708 : Nat := 118140960795 + 2770708 * 2 ^ 59
def prefixEnd_2770708 : Nat := 4983230072969 + 3 ^ 40 * 2770708 * 2
def baseEnd_2770708 : Nat := 1422704957257650825907753

theorem tailTrace_2770708 : CollatzResearch.WordTrace tailWord_2770708 prefixEnd_2770708 1422704957257650825907753 := by
  unfold tailWord_2770708
  simp only [CollatzResearch.WordTrace]
  refine ⟨50528011423102795049096389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67370681897470393398795185 50528011423102795049096389)
  ·
    refine ⟨9474002141831774071705573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50528011423102795049096389 9474002141831774071705573)
    ·
      refine ⟨1776375401593457638444795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9474002141831774071705573 1776375401593457638444795)
      ·
        refine ⟨2664563102390186457667193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1776375401593457638444795 2664563102390186457667193)
        ·
          refine ⟨1998422326792639843250395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2664563102390186457667193 1998422326792639843250395)
          ·
            refine ⟨2997633490188959764875593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1998422326792639843250395 2997633490188959764875593)
            ·
              refine ⟨2248225117641719823656695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2997633490188959764875593 2248225117641719823656695)
              ·
                refine ⟨3372337676462579735485043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2248225117641719823656695 3372337676462579735485043)
                ·
                  refine ⟨5058506514693869603227565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3372337676462579735485043 5058506514693869603227565)
                  ·
                    refine ⟨1896939943010201101210337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5058506514693869603227565 1896939943010201101210337)
                    ·
                      refine ⟨1422704957257650825907753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1896939943010201101210337 1422704957257650825907753)
                      ·
                        rfl

theorem cell23_2770708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_2770708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770708 prefixEnd_2770708 := by exact prefixLift 2770708
  have htrace : WordTrace (prefixWord ++ tailWord_2770708) baseStart_2770708 baseEnd_2770708 := by
    simpa [prefixWord, tailWord_2770708, baseEnd_2770708] using wordTrace_append hprefix tailTrace_2770708
  have hstable : (prefixWord ++ tailWord_2770708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770708).length < 2 ^ (prefixWord ++ tailWord_2770708).sum := by decide
  have hdescent : baseEnd_2770708 < baseStart_2770708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770729 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 5, 4, 3]
def baseStart_2770729 : Nat := 118140960795 + 2770729 * 2 ^ 59
def prefixEnd_2770729 : Nat := 4983230072969 + 3 ^ 40 * 2770729 * 2
def baseEnd_2770729 : Nat := 1422715740351395243745155

theorem tailTrace_2770729 : CollatzResearch.WordTrace tailWord_2770729 prefixEnd_2770729 1422715740351395243745155 := by
  unfold tailWord_2770729
  simp only [CollatzResearch.WordTrace]
  refine ⟨101056788779129510684707241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67371192519419673789804827 101056788779129510684707241)
  ·
    refine ⟨75792591584347133013530431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101056788779129510684707241 75792591584347133013530431)
    ·
      refine ⟨113688887376520699520295647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75792591584347133013530431 113688887376520699520295647)
      ·
        refine ⟨170533331064781049280443471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113688887376520699520295647 170533331064781049280443471)
        ·
          refine ⟨255799996597171573920665207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170533331064781049280443471 255799996597171573920665207)
          ·
            refine ⟨383699994895757360880997811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255799996597171573920665207 383699994895757360880997811)
            ·
              refine ⟨575549992343636041321496717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 383699994895757360880997811 575549992343636041321496717)
              ·
                refine ⟨215831247128863515495561269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 575549992343636041321496717 215831247128863515495561269)
                ·
                  refine ⟨20234179418330954577708869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 215831247128863515495561269 20234179418330954577708869)
                  ·
                    refine ⟨3793908640937053983320413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20234179418330954577708869 3793908640937053983320413)
                    ·
                      refine ⟨1422715740351395243745155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3793908640937053983320413 1422715740351395243745155)
                      ·
                        rfl

theorem cell23_2770729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 4, 3].length) (baseStart_2770729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770729 prefixEnd_2770729 := by exact prefixLift 2770729
  have htrace : WordTrace (prefixWord ++ tailWord_2770729) baseStart_2770729 baseEnd_2770729 := by
    simpa [prefixWord, tailWord_2770729, baseEnd_2770729] using wordTrace_append hprefix tailTrace_2770729
  have hstable : (prefixWord ++ tailWord_2770729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770729).length < 2 ^ (prefixWord ++ tailWord_2770729).sum := by decide
  have hdescent : baseEnd_2770729 < baseStart_2770729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770746 : List Nat := [3, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3]
def baseStart_2770746 : Nat := 118140960795 + 2770746 * 2 ^ 59
def prefixEnd_2770746 : Nat := 4983230072969 + 3 ^ 40 * 2770746 * 2
def baseEnd_2770746 : Nat := 1422724469522521677232577

theorem tailTrace_2770746 : CollatzResearch.WordTrace tailWord_2770746 prefixEnd_2770746 1422724469522521677232577 := by
  unfold tailWord_2770746
  simp only [CollatzResearch.WordTrace]
  refine ⟨25264352205016980647019023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67371605880045281725384061 25264352205016980647019023)
  ·
    refine ⟨37896528307525470970528535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25264352205016980647019023 37896528307525470970528535)
    ·
      refine ⟨56844792461288206455792803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37896528307525470970528535 56844792461288206455792803)
      ·
        refine ⟨85267188691932309683689205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56844792461288206455792803 85267188691932309683689205)
        ·
          refine ⟨7993798939868654032845863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85267188691932309683689205 7993798939868654032845863)
          ·
            refine ⟨11990698409802981049268795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7993798939868654032845863 11990698409802981049268795)
            ·
              refine ⟨17986047614704471573903193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11990698409802981049268795 17986047614704471573903193)
              ·
                refine ⟨13489535711028353680427395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17986047614704471573903193 13489535711028353680427395)
                ·
                  refine ⟨20234303566542530520641093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13489535711028353680427395 20234303566542530520641093)
                  ·
                    refine ⟨3793931918726724472620205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20234303566542530520641093 3793931918726724472620205)
                    ·
                      refine ⟨1422724469522521677232577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3793931918726724472620205 1422724469522521677232577)
                      ·
                        rfl

theorem cell23_2770746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3].length) (baseStart_2770746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770746 prefixEnd_2770746 := by exact prefixLift 2770746
  have htrace : WordTrace (prefixWord ++ tailWord_2770746) baseStart_2770746 baseEnd_2770746 := by
    simpa [prefixWord, tailWord_2770746, baseEnd_2770746] using wordTrace_append hprefix tailTrace_2770746
  have hstable : (prefixWord ++ tailWord_2770746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770746).length < 2 ^ (prefixWord ++ tailWord_2770746).sum := by decide
  have hdescent : baseEnd_2770746 < baseStart_2770746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770770 : List Nat := [3, 2, 2, 1, 1, 3, 3, 3, 1, 4]
def baseStart_2770770 : Nat := 118140960795 + 2770770 * 2 ^ 59
def prefixEnd_2770770 : Nat := 4983230072969 + 3 ^ 40 * 2770770 * 2
def baseEnd_2770770 : Nat := 474245597686076527777489

theorem tailTrace_2770770 : CollatzResearch.WordTrace tailWord_2770770 prefixEnd_2770770 474245597686076527777489 := by
  unfold tailWord_2770770
  simp only [CollatzResearch.WordTrace]
  refine ⟨25264571042995243671737441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67372189447987316457966509 25264571042995243671737441)
  ·
    refine ⟨18948428282246432753803081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25264571042995243671737441 18948428282246432753803081)
    ·
      refine ⟨14211321211684824565352311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18948428282246432753803081 14211321211684824565352311)
      ·
        refine ⟨21316981817527236848028467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14211321211684824565352311 21316981817527236848028467)
        ·
          refine ⟨31975472726290855272042701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21316981817527236848028467 31975472726290855272042701)
          ·
            refine ⟨11990802272359070727016013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31975472726290855272042701 11990802272359070727016013)
            ·
              refine ⟨4496550852134651522631005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11990802272359070727016013 4496550852134651522631005)
              ·
                refine ⟨1686206569550494320986627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4496550852134651522631005 1686206569550494320986627)
                ·
                  refine ⟨2529309854325741481479941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1686206569550494320986627 2529309854325741481479941)
                  ·
                    refine ⟨474245597686076527777489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2529309854325741481479941 474245597686076527777489)
                    ·
                      rfl

theorem cell23_2770770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_2770770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770770 prefixEnd_2770770 := by exact prefixLift 2770770
  have htrace : WordTrace (prefixWord ++ tailWord_2770770) baseStart_2770770 baseEnd_2770770 := by
    simpa [prefixWord, tailWord_2770770, baseEnd_2770770] using wordTrace_append hprefix tailTrace_2770770
  have hstable : (prefixWord ++ tailWord_2770770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770770).length < 2 ^ (prefixWord ++ tailWord_2770770).sum := by decide
  have hdescent : baseEnd_2770770 < baseStart_2770770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770780 : List Nat := [2, 2, 4, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_2770780 : Nat := 118140960795 + 2770780 * 2 ^ 59
def prefixEnd_2770780 : Nat := 4983230072969 + 3 ^ 40 * 2770780 * 2
def baseEnd_2770780 : Nat := 1422741927864774544207421

theorem tailTrace_2770780 : CollatzResearch.WordTrace tailWord_2770780 prefixEnd_2770780 1422741927864774544207421 := by
  unfold tailWord_2770780
  simp only [CollatzResearch.WordTrace]
  refine ⟨50529324450972373197406897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67372432601296497596542529 50529324450972373197406897)
  ·
    refine ⟨37896993338229279898055173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50529324450972373197406897 37896993338229279898055173)
    ·
      refine ⟨7105686250917989980885345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37896993338229279898055173 7105686250917989980885345)
      ·
        refine ⟨5329264688188492485664009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7105686250917989980885345 5329264688188492485664009)
        ·
          refine ⟨3996948516141369364248007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5329264688188492485664009 3996948516141369364248007)
          ·
            refine ⟨5995422774212054046372011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3996948516141369364248007 5995422774212054046372011)
            ·
              refine ⟨8993134161318081069558017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5995422774212054046372011 8993134161318081069558017)
              ·
                refine ⟨6744850620988560802168513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8993134161318081069558017 6744850620988560802168513)
                ·
                  refine ⟨5058637965741420601626385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6744850620988560802168513 5058637965741420601626385)
                  ·
                    refine ⟨3793978474306065451219789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5058637965741420601626385 3793978474306065451219789)
                    ·
                      refine ⟨1422741927864774544207421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3793978474306065451219789 1422741927864774544207421)
                      ·
                        rfl

theorem cell23_2770780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_2770780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770780 prefixEnd_2770780 := by exact prefixLift 2770780
  have htrace : WordTrace (prefixWord ++ tailWord_2770780) baseStart_2770780 baseEnd_2770780 := by
    simpa [prefixWord, tailWord_2770780, baseEnd_2770780] using wordTrace_append hprefix tailTrace_2770780
  have hstable : (prefixWord ++ tailWord_2770780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770780).length < 2 ^ (prefixWord ++ tailWord_2770780).sum := by decide
  have hdescent : baseEnd_2770780 < baseStart_2770780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770787 : List Nat := [1, 1, 1, 5, 4, 1, 3, 2, 1, 4]
def baseStart_2770787 : Nat := 118140960795 + 2770787 * 2 ^ 59
def prefixEnd_2770787 : Nat := 4983230072969 + 3 ^ 40 * 2770787 * 2
def baseEnd_2770787 : Nat := 474248507409785338939963

theorem tailTrace_2770787 : CollatzResearch.WordTrace tailWord_2770787 prefixEnd_2770787 474248507409785338939963 := by
  unfold tailWord_2770787
  simp only [CollatzResearch.WordTrace]
  refine ⟨101058904212919386590318615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67372602808612924393545743 101058904212919386590318615)
  ·
    refine ⟨151588356319379079885477923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101058904212919386590318615 151588356319379079885477923)
    ·
      refine ⟨227382534479068619828216885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151588356319379079885477923 227382534479068619828216885)
      ·
        refine ⟨21317112607412683108895333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 227382534479068619828216885 21317112607412683108895333)
        ·
          refine ⟨3996958613889878082917875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21317112607412683108895333 3996958613889878082917875)
          ·
            refine ⟨5995437920834817124376813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3996958613889878082917875 5995437920834817124376813)
            ·
              refine ⟨2248289220313056421641305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5995437920834817124376813 2248289220313056421641305)
              ·
                refine ⟨1686216915234792316230979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2248289220313056421641305 1686216915234792316230979)
                ·
                  refine ⟨2529325372852188474346469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1686216915234792316230979 2529325372852188474346469)
                  ·
                    refine ⟨474248507409785338939963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2529325372852188474346469 474248507409785338939963)
                    ·
                      rfl

theorem cell23_2770787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2, 1, 4].length) (baseStart_2770787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770787 prefixEnd_2770787 := by exact prefixLift 2770787
  have htrace : WordTrace (prefixWord ++ tailWord_2770787) baseStart_2770787 baseEnd_2770787 := by
    simpa [prefixWord, tailWord_2770787, baseEnd_2770787] using wordTrace_append hprefix tailTrace_2770787
  have hstable : (prefixWord ++ tailWord_2770787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770787).length < 2 ^ (prefixWord ++ tailWord_2770787).sum := by decide
  have hdescent : baseEnd_2770787 < baseStart_2770787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770789 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 2, 1, 7]
def baseStart_2770789 : Nat := 118140960795 + 2770789 * 2 ^ 59
def prefixEnd_2770789 : Nat := 4983230072969 + 3 ^ 40 * 2770789 * 2
def baseEnd_2770789 : Nat := 1422746549190665008994879

theorem tailTrace_2770789 : CollatzResearch.WordTrace tailWord_2770789 prefixEnd_2770789 1422746549190665008994879 := by
  unfold tailWord_2770789
  simp only [CollatzResearch.WordTrace]
  refine ⟨101058977158912140931891421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67372651439274760621260947 101058977158912140931891421)
  ·
    refine ⟨37897116434592052849459283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101058977158912140931891421 37897116434592052849459283)
    ·
      refine ⟨56845674651888079274188925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37897116434592052849459283 56845674651888079274188925)
      ·
        refine ⟨21317127994458029727820847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56845674651888079274188925 21317127994458029727820847)
        ·
          refine ⟨31975691991687044591731271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21317127994458029727820847 31975691991687044591731271)
          ·
            refine ⟨47963537987530566887596907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31975691991687044591731271 47963537987530566887596907)
            ·
              refine ⟨71945306981295850331395361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47963537987530566887596907 71945306981295850331395361)
              ·
                refine ⟨53958980235971887748546521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71945306981295850331395361 53958980235971887748546521)
                ·
                  refine ⟨40469235176978915811409891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53958980235971887748546521 40469235176978915811409891)
                  ·
                    refine ⟨60703852765468373717114837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40469235176978915811409891 60703852765468373717114837)
                    ·
                      refine ⟨1422746549190665008994879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60703852765468373717114837 1422746549190665008994879)
                      ·
                        rfl

theorem cell23_2770789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_2770789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770789 prefixEnd_2770789 := by exact prefixLift 2770789
  have htrace : WordTrace (prefixWord ++ tailWord_2770789) baseStart_2770789 baseEnd_2770789 := by
    simpa [prefixWord, tailWord_2770789, baseEnd_2770789] using wordTrace_append hprefix tailTrace_2770789
  have hstable : (prefixWord ++ tailWord_2770789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770789).length < 2 ^ (prefixWord ++ tailWord_2770789).sum := by decide
  have hdescent : baseEnd_2770789 < baseStart_2770789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770799 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 4]
def baseStart_2770799 : Nat := 118140960795 + 2770799 * 2 ^ 59
def prefixEnd_2770799 : Nat := 4983230072969 + 3 ^ 40 * 2770799 * 2
def baseEnd_2770799 : Nat := 1422751683997209969869833

theorem tailTrace_2770799 : CollatzResearch.WordTrace tailWord_2770799 prefixEnd_2770799 1422751683997209969869833 := by
  unfold tailWord_2770799
  simp only [CollatzResearch.WordTrace]
  refine ⟨101059341888875912639755451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67372894592583941759836967 101059341888875912639755451)
  ·
    refine ⟨151589012833313868959633177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101059341888875912639755451 151589012833313868959633177)
    ·
      refine ⟨113691759624985401719724883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151589012833313868959633177 113691759624985401719724883)
      ·
        refine ⟨170537639437478102579587325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113691759624985401719724883 170537639437478102579587325)
        ·
          refine ⟨63951614789054288467345247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170537639437478102579587325 63951614789054288467345247)
          ·
            refine ⟨95927422183581432701017871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63951614789054288467345247 95927422183581432701017871)
            ·
              refine ⟨143891133275372149051526807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95927422183581432701017871 143891133275372149051526807)
              ·
                refine ⟨215836699913058223577290211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143891133275372149051526807 215836699913058223577290211)
                ·
                  refine ⟨323755049869587335365935317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215836699913058223577290211 323755049869587335365935317)
                  ·
                    refine ⟨7588008981318453172639109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 323755049869587335365935317 7588008981318453172639109)
                    ·
                      refine ⟨1422751683997209969869833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7588008981318453172639109 1422751683997209969869833)
                      ·
                        rfl

theorem cell23_2770799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 4].length) (baseStart_2770799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770799 prefixEnd_2770799 := by exact prefixLift 2770799
  have htrace : WordTrace (prefixWord ++ tailWord_2770799) baseStart_2770799 baseEnd_2770799 := by
    simpa [prefixWord, tailWord_2770799, baseEnd_2770799] using wordTrace_append hprefix tailTrace_2770799
  have hstable : (prefixWord ++ tailWord_2770799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770799).length < 2 ^ (prefixWord ++ tailWord_2770799).sum := by decide
  have hdescent : baseEnd_2770799 < baseStart_2770799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770816 : List Nat := [2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 4]
def baseStart_2770816 : Nat := 118140960795 + 2770816 * 2 ^ 59
def prefixEnd_2770816 : Nat := 4983230072969 + 3 ^ 40 * 2770816 * 2
def baseEnd_2770816 : Nat := 1422760413168336403357255

theorem tailTrace_2770816 : CollatzResearch.WordTrace tailWord_2770816 prefixEnd_2770816 1422760413168336403357255 := by
  unfold tailWord_2770816
  simp only [CollatzResearch.WordTrace]
  refine ⟨50529980964907162271562151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67373307953209549695416201 50529980964907162271562151)
  ·
    refine ⟨75794971447360743407343227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50529980964907162271562151 75794971447360743407343227)
    ·
      refine ⟨113692457171041115111014841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75794971447360743407343227 113692457171041115111014841)
      ·
        refine ⟨85269342878280836333261131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113692457171041115111014841 85269342878280836333261131)
        ·
          refine ⟨127904014317421254499891697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85269342878280836333261131 127904014317421254499891697)
          ·
            refine ⟨95928010738065940874918773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127904014317421254499891697 95928010738065940874918773)
            ·
              refine ⟨8993251006693681957023635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95928010738065940874918773 8993251006693681957023635)
              ·
                refine ⟨13489876510040522935535453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8993251006693681957023635 13489876510040522935535453)
                ·
                  refine ⟨5058703691265196100825795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13489876510040522935535453 5058703691265196100825795)
                  ·
                    refine ⟨7588055536897794151238693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5058703691265196100825795 7588055536897794151238693)
                    ·
                      refine ⟨1422760413168336403357255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7588055536897794151238693 1422760413168336403357255)
                      ·
                        rfl

theorem cell23_2770816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_2770816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770816 prefixEnd_2770816 := by exact prefixLift 2770816
  have htrace : WordTrace (prefixWord ++ tailWord_2770816) baseStart_2770816 baseEnd_2770816 := by
    simpa [prefixWord, tailWord_2770816, baseEnd_2770816] using wordTrace_append hprefix tailTrace_2770816
  have hstable : (prefixWord ++ tailWord_2770816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770816).length < 2 ^ (prefixWord ++ tailWord_2770816).sum := by decide
  have hdescent : baseEnd_2770816 < baseStart_2770816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770838 : List Nat := [5, 3, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_2770838 : Nat := 118140960795 + 2770838 * 2 ^ 59
def prefixEnd_2770838 : Nat := 4983230072969 + 3 ^ 40 * 2770838 * 2
def baseEnd_2770838 : Nat := 474257236580911772427385

theorem tailTrace_2770838 : CollatzResearch.WordTrace tailWord_2770838 prefixEnd_2770838 474257236580911772427385 := by
  unfold tailWord_2770838
  simp only [CollatzResearch.WordTrace]
  refine ⟨6316297770983413893776573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67373842890489748200283445 6316297770983413893776573)
  ·
    refine ⟨2368611664118780210166215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6316297770983413893776573 2368611664118780210166215)
    ·
      refine ⟨3552917496178170315249323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2368611664118780210166215 3552917496178170315249323)
      ·
        refine ⟨5329376244267255472873985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3552917496178170315249323 5329376244267255472873985)
        ·
          refine ⟨3997032183200441604655489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5329376244267255472873985 3997032183200441604655489)
          ·
            refine ⟨2997774137400331203491617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3997032183200441604655489 2997774137400331203491617)
            ·
              refine ⟨2248330603050248402618713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2997774137400331203491617 2248330603050248402618713)
              ·
                refine ⟨1686247952287686301964035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2248330603050248402618713 1686247952287686301964035)
                ·
                  refine ⟨2529371928431529452946053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1686247952287686301964035 2529371928431529452946053)
                  ·
                    refine ⟨474257236580911772427385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2529371928431529452946053 474257236580911772427385)
                    ·
                      rfl

theorem cell23_2770838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_2770838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770838 prefixEnd_2770838 := by exact prefixLift 2770838
  have htrace : WordTrace (prefixWord ++ tailWord_2770838) baseStart_2770838 baseEnd_2770838 := by
    simpa [prefixWord, tailWord_2770838, baseEnd_2770838] using wordTrace_append hprefix tailTrace_2770838
  have hstable : (prefixWord ++ tailWord_2770838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770838).length < 2 ^ (prefixWord ++ tailWord_2770838).sum := by decide
  have hdescent : baseEnd_2770838 < baseStart_2770838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770839 : List Nat := [1, 1, 3, 3, 1, 14]
def baseStart_2770839 : Nat := 118140960795 + 2770839 * 2 ^ 59
def prefixEnd_2770839 : Nat := 4983230072969 + 3 ^ 40 * 2770839 * 2
def baseEnd_2770839 : Nat := 5855029725199135034443

theorem tailTrace_2770839 : CollatzResearch.WordTrace tailWord_2770839 prefixEnd_2770839 5855029725199135034443 := by
  unfold tailWord_2770839
  simp only [CollatzResearch.WordTrace]
  refine ⟨101060800808730999471211571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67373867205820666314141047 101060800808730999471211571)
  ·
    refine ⟨151591201213096499206817357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101060800808730999471211571 151591201213096499206817357)
    ·
      refine ⟨56846700454911187202556509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151591201213096499206817357 56846700454911187202556509)
      ·
        refine ⟨21317512670591695200958691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56846700454911187202556509 21317512670591695200958691)
        ·
          refine ⟨31976269005887542801438037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21317512670591695200958691 31976269005887542801438037)
          ·
            refine ⟨5855029725199135034443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 31976269005887542801438037 5855029725199135034443)
            ·
              rfl

theorem cell23_2770839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 14].length) (baseStart_2770839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770839 prefixEnd_2770839 := by exact prefixLift 2770839
  have htrace : WordTrace (prefixWord ++ tailWord_2770839) baseStart_2770839 baseEnd_2770839 := by
    simpa [prefixWord, tailWord_2770839, baseEnd_2770839] using wordTrace_append hprefix tailTrace_2770839
  have hstable : (prefixWord ++ tailWord_2770839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770839).length < 2 ^ (prefixWord ++ tailWord_2770839).sum := by decide
  have hdescent : baseEnd_2770839 < baseStart_2770839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770844 : List Nat := [2, 2, 3, 3, 1, 1, 4, 2, 1, 1, 3]
def baseStart_2770844 : Nat := 118140960795 + 2770844 * 2 ^ 59
def prefixEnd_2770844 : Nat := 4983230072969 + 3 ^ 40 * 2770844 * 2
def baseEnd_2770844 : Nat := 1422774790626662293807127

theorem tailTrace_2770844 : CollatzResearch.WordTrace tailWord_2770844 prefixEnd_2770844 1422774790626662293807127 := by
  unfold tailWord_2770844
  simp only [CollatzResearch.WordTrace]
  refine ⟨50530491586856442662571793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67373988782475256883429057 50530491586856442662571793)
  ·
    refine ⟨37897868690142331996928845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50530491586856442662571793 37897868690142331996928845)
    ·
      refine ⟨14211700758803374498848317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37897868690142331996928845 14211700758803374498848317)
      ·
        refine ⟨5329387784551265437068119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14211700758803374498848317 5329387784551265437068119)
        ·
          refine ⟨7994081676826898155602179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5329387784551265437068119 7994081676826898155602179)
          ·
            refine ⟨11991122515240347233403269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7994081676826898155602179 11991122515240347233403269)
            ·
              refine ⟨2248335471607565106263113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11991122515240347233403269 2248335471607565106263113)
              ·
                refine ⟨1686251603705673829697335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2248335471607565106263113 1686251603705673829697335)
                ·
                  refine ⟨2529377405558510744546003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1686251603705673829697335 2529377405558510744546003)
                  ·
                    refine ⟨3794066108337766116819005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2529377405558510744546003 3794066108337766116819005)
                    ·
                      refine ⟨1422774790626662293807127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3794066108337766116819005 1422774790626662293807127)
                      ·
                        rfl

theorem cell23_2770844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_2770844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770844 prefixEnd_2770844 := by exact prefixLift 2770844
  have htrace : WordTrace (prefixWord ++ tailWord_2770844) baseStart_2770844 baseEnd_2770844 := by
    simpa [prefixWord, tailWord_2770844, baseEnd_2770844] using wordTrace_append hprefix tailTrace_2770844
  have hstable : (prefixWord ++ tailWord_2770844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770844).length < 2 ^ (prefixWord ++ tailWord_2770844).sum := by decide
  have hdescent : baseEnd_2770844 < baseStart_2770844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770900 : List Nat := [2, 4, 1, 2, 1, 1, 3, 1, 4, 1, 3]
def baseStart_2770900 : Nat := 118140960795 + 2770900 * 2 ^ 59
def prefixEnd_2770900 : Nat := 4983230072969 + 3 ^ 40 * 2770900 * 2
def baseEnd_2770900 : Nat := 1422803545543314074706869

theorem tailTrace_2770900 : CollatzResearch.WordTrace tailWord_2770900 prefixEnd_2770900 1422803545543314074706869 := by
  unfold tailWord_2770900
  simp only [CollatzResearch.WordTrace]
  refine ⟨50531512830755003444591077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67375350441006671259454769 50531512830755003444591077)
  ·
    refine ⟨9474658655766563145860827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50531512830755003444591077 9474658655766563145860827)
    ·
      refine ⟨14211987983649844718791241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9474658655766563145860827 14211987983649844718791241)
      ·
        refine ⟨10658990987737383539093431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14211987983649844718791241 10658990987737383539093431)
        ·
          refine ⟨15988486481606075308640147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10658990987737383539093431 15988486481606075308640147)
          ·
            refine ⟨23982729722409112962960221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15988486481606075308640147 23982729722409112962960221)
            ·
              refine ⟨8993523645903417361110083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23982729722409112962960221 8993523645903417361110083)
              ·
                refine ⟨13490285468855126041665125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8993523645903417361110083 13490285468855126041665125)
                ·
                  refine ⟨2529428525410336132812211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13490285468855126041665125 2529428525410336132812211)
                  ·
                    refine ⟨3794142788115504199218317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2529428525410336132812211 3794142788115504199218317)
                    ·
                      refine ⟨1422803545543314074706869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3794142788115504199218317 1422803545543314074706869)
                      ·
                        rfl

theorem cell23_2770900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_2770900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770900 prefixEnd_2770900 := by exact prefixLift 2770900
  have htrace : WordTrace (prefixWord ++ tailWord_2770900) baseStart_2770900 baseEnd_2770900 := by
    simpa [prefixWord, tailWord_2770900, baseEnd_2770900] using wordTrace_append hprefix tailTrace_2770900
  have hstable : (prefixWord ++ tailWord_2770900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770900).length < 2 ^ (prefixWord ++ tailWord_2770900).sum := by decide
  have hdescent : baseEnd_2770900 < baseStart_2770900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770914 : List Nat := [3, 3, 3, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_2770914 : Nat := 118140960795 + 2770914 * 2 ^ 59
def prefixEnd_2770914 : Nat := 4983230072969 + 3 ^ 40 * 2770914 * 2
def baseEnd_2770914 : Nat := 1422810734272477019931805

theorem tailTrace_2770914 : CollatzResearch.WordTrace tailWord_2770914 prefixEnd_2770914 1422810734272477019931805 := by
  unfold tailWord_2770914
  simp only [CollatzResearch.WordTrace]
  refine ⟨25265884070864821820047949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67375690855639524853461197 25265884070864821820047949)
  ·
    refine ⟨9474706526574308182517981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25265884070864821820047949 9474706526574308182517981)
    ·
      refine ⟨3553014947465365568444243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9474706526574308182517981 3553014947465365568444243)
      ·
        refine ⟨5329522421198048352666365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3553014947465365568444243 5329522421198048352666365)
        ·
          refine ⟨1998570907949268132249887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5329522421198048352666365 1998570907949268132249887)
          ·
            refine ⟨2997856361923902198374831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1998570907949268132249887 2997856361923902198374831)
            ·
              refine ⟨4496784542885853297562247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2997856361923902198374831 4496784542885853297562247)
              ·
                refine ⟨6745176814328779946343371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4496784542885853297562247 6745176814328779946343371)
                ·
                  refine ⟨10117765221493169919515057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6745176814328779946343371 10117765221493169919515057)
                  ·
                    refine ⟨7588323916119877439636293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10117765221493169919515057 7588323916119877439636293)
                    ·
                      refine ⟨1422810734272477019931805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7588323916119877439636293 1422810734272477019931805)
                      ·
                        rfl

theorem cell23_2770914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_2770914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770914 prefixEnd_2770914 := by exact prefixLift 2770914
  have htrace : WordTrace (prefixWord ++ tailWord_2770914) baseStart_2770914 baseEnd_2770914 := by
    simpa [prefixWord, tailWord_2770914, baseEnd_2770914] using wordTrace_append hprefix tailTrace_2770914
  have hstable : (prefixWord ++ tailWord_2770914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770914).length < 2 ^ (prefixWord ++ tailWord_2770914).sum := by decide
  have hdescent : baseEnd_2770914 < baseStart_2770914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770916 : List Nat := [2, 3, 1, 1, 1, 1, 3, 3, 2, 6]
def baseStart_2770916 : Nat := 118140960795 + 2770916 * 2 ^ 59
def prefixEnd_2770916 : Nat := 4983230072969 + 3 ^ 40 * 2770916 * 2
def baseEnd_2770916 : Nat := 474270587077928670702265

theorem tailTrace_2770916 : CollatzResearch.WordTrace tailWord_2770916 prefixEnd_2770916 474270587077928670702265 := by
  unfold tailWord_2770916
  simp only [CollatzResearch.WordTrace]
  refine ⟨50531804614726020810882301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67375739486301361081176401 50531804614726020810882301)
  ·
    refine ⟨18949426730522257804080863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50531804614726020810882301 18949426730522257804080863)
    ·
      refine ⟨28424140095783386706121295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18949426730522257804080863 28424140095783386706121295)
      ·
        refine ⟨42636210143675080059181943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28424140095783386706121295 42636210143675080059181943)
        ·
          refine ⟨63954315215512620088772915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42636210143675080059181943 63954315215512620088772915)
          ·
            refine ⟨95931472823268930133159373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63954315215512620088772915 95931472823268930133159373)
            ·
              refine ⟨35974302308725848799934765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95931472823268930133159373 35974302308725848799934765)
              ·
                refine ⟨13490363365772193299975537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35974302308725848799934765 13490363365772193299975537)
                ·
                  refine ⟨10117772524329144974981653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13490363365772193299975537 10117772524329144974981653)
                  ·
                    refine ⟨474270587077928670702265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10117772524329144974981653 474270587077928670702265)
                    ·
                      rfl

theorem cell23_2770916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_2770916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770916 prefixEnd_2770916 := by exact prefixLift 2770916
  have htrace : WordTrace (prefixWord ++ tailWord_2770916) baseStart_2770916 baseEnd_2770916 := by
    simpa [prefixWord, tailWord_2770916, baseEnd_2770916] using wordTrace_append hprefix tailTrace_2770916
  have hstable : (prefixWord ++ tailWord_2770916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770916).length < 2 ^ (prefixWord ++ tailWord_2770916).sum := by decide
  have hdescent : baseEnd_2770916 < baseStart_2770916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770936 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 1, 4, 4]
def baseStart_2770936 : Nat := 118140960795 + 2770936 * 2 ^ 59
def prefixEnd_2770936 : Nat := 4983230072969 + 3 ^ 40 * 2770936 * 2
def baseEnd_2770936 : Nat := 1422822030846875933856703

theorem tailTrace_2770936 : CollatzResearch.WordTrace tailWord_2770936 prefixEnd_2770936 1422822030846875933856703 := by
  unfold tailWord_2770936
  simp only [CollatzResearch.WordTrace]
  refine ⟨50532169344689792518746331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67376225792919723358328441 50532169344689792518746331)
  ·
    refine ⟨75798254017034688778119497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50532169344689792518746331 75798254017034688778119497)
    ·
      refine ⟨56848690512776016583589623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75798254017034688778119497 56848690512776016583589623)
      ·
        refine ⟨85273035769164024875384435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56848690512776016583589623 85273035769164024875384435)
        ·
          refine ⟨127909553653746037313076653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85273035769164024875384435 127909553653746037313076653)
          ·
            refine ⟨47966082620154763992403745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127909553653746037313076653 47966082620154763992403745)
            ·
              refine ⟨35974561965116072994302809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47966082620154763992403745 35974561965116072994302809)
              ·
                refine ⟨26980921473837054745727107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35974561965116072994302809 26980921473837054745727107)
                ·
                  refine ⟨40471382210755582118590661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26980921473837054745727107 40471382210755582118590661)
                  ·
                    refine ⟨7588384164516671647235749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40471382210755582118590661 7588384164516671647235749)
                    ·
                      refine ⟨1422822030846875933856703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7588384164516671647235749 1422822030846875933856703)
                      ·
                        rfl

theorem cell23_2770936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_2770936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770936 prefixEnd_2770936 := by exact prefixLift 2770936
  have htrace : WordTrace (prefixWord ++ tailWord_2770936) baseStart_2770936 baseEnd_2770936 := by
    simpa [prefixWord, tailWord_2770936, baseEnd_2770936] using wordTrace_append hprefix tailTrace_2770936
  have hstable : (prefixWord ++ tailWord_2770936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770936).length < 2 ^ (prefixWord ++ tailWord_2770936).sum := by decide
  have hdescent : baseEnd_2770936 < baseStart_2770936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770940 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 6, 2, 2]
def baseStart_2770940 : Nat := 118140960795 + 2770940 * 2 ^ 59
def prefixEnd_2770940 : Nat := 4983230072969 + 3 ^ 40 * 2770940 * 2
def baseEnd_2770940 : Nat := 1422824084769493918206685

theorem tailTrace_2770940 : CollatzResearch.WordTrace tailWord_2770940 prefixEnd_2770940 1422824084769493918206685 := by
  unfold tailWord_2770940
  simp only [CollatzResearch.WordTrace]
  refine ⟨50532242290682546860319137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67376323054243395813758849 50532242290682546860319137)
  ·
    refine ⟨37899181718011910145239353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50532242290682546860319137 37899181718011910145239353)
    ·
      refine ⟨28424386288508932608929515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37899181718011910145239353 28424386288508932608929515)
      ·
        refine ⟨42636579432763398913394273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28424386288508932608929515 42636579432763398913394273)
        ·
          refine ⟨31977434574572549185045705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42636579432763398913394273 31977434574572549185045705)
          ·
            refine ⟨23983075930929411888784279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31977434574572549185045705 23983075930929411888784279)
            ·
              refine ⟨35974613896394117833176419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23983075930929411888784279 35974613896394117833176419)
              ·
                refine ⟨53961920844591176749764629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35974613896394117833176419 53961920844591176749764629)
                ·
                  refine ⟨2529465039590211410145217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53961920844591176749764629 2529465039590211410145217)
                  ·
                    refine ⟨1897098779692658557608913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2529465039590211410145217 1897098779692658557608913)
                    ·
                      refine ⟨1422824084769493918206685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1897098779692658557608913 1422824084769493918206685)
                      ·
                        rfl

theorem cell23_2770940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 6, 2, 2].length) (baseStart_2770940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770940 prefixEnd_2770940 := by exact prefixLift 2770940
  have htrace : WordTrace (prefixWord ++ tailWord_2770940) baseStart_2770940 baseEnd_2770940 := by
    simpa [prefixWord, tailWord_2770940, baseEnd_2770940] using wordTrace_append hprefix tailTrace_2770940
  have hstable : (prefixWord ++ tailWord_2770940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770940).length < 2 ^ (prefixWord ++ tailWord_2770940).sum := by decide
  have hdescent : baseEnd_2770940 < baseStart_2770940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770956 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 1, 2, 7]
def baseStart_2770956 : Nat := 118140960795 + 2770956 * 2 ^ 59
def prefixEnd_2770956 : Nat := 4983230072969 + 3 ^ 40 * 2770956 * 2
def baseEnd_2770956 : Nat := 1422832300459965855606611

theorem tailTrace_2770956 : CollatzResearch.WordTrace tailWord_2770956 prefixEnd_2770956 1422832300459965855606611 := by
  unfold tailWord_2770956
  simp only [CollatzResearch.WordTrace]
  refine ⟨50532534074653564226610361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67376712099538085635480481 50532534074653564226610361)
  ·
    refine ⟨37899400555990173169957771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50532534074653564226610361 37899400555990173169957771)
    ·
      refine ⟨56849100833985259754936657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37899400555990173169957771 56849100833985259754936657)
      ·
        refine ⟨42636825625488944816202493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56849100833985259754936657 42636825625488944816202493)
        ·
          refine ⟨15988809609558354306075935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42636825625488944816202493 15988809609558354306075935)
          ·
            refine ⟨23983214414337531459113903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15988809609558354306075935 23983214414337531459113903)
            ·
              refine ⟨35974821621506297188670855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23983214414337531459113903 35974821621506297188670855)
              ·
                refine ⟨53962232432259445783006283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35974821621506297188670855 53962232432259445783006283)
                ·
                  refine ⟨80943348648389168674509425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53962232432259445783006283 80943348648389168674509425)
                  ·
                    refine ⟨60707511486291876505882069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80943348648389168674509425 60707511486291876505882069)
                    ·
                      refine ⟨1422832300459965855606611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60707511486291876505882069 1422832300459965855606611)
                      ·
                        rfl

theorem cell23_2770956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_2770956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770956 prefixEnd_2770956 := by exact prefixLift 2770956
  have htrace : WordTrace (prefixWord ++ tailWord_2770956) baseStart_2770956 baseEnd_2770956 := by
    simpa [prefixWord, tailWord_2770956, baseEnd_2770956] using wordTrace_append hprefix tailTrace_2770956
  have hstable : (prefixWord ++ tailWord_2770956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770956).length < 2 ^ (prefixWord ++ tailWord_2770956).sum := by decide
  have hdescent : baseEnd_2770956 < baseStart_2770956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770963 : List Nat := [1, 1, 1, 2, 1, 4, 2, 6, 5]
def baseStart_2770963 : Nat := 118140960795 + 2770963 * 2 ^ 59
def prefixEnd_2770963 : Nat := 4983230072969 + 3 ^ 40 * 2770963 * 2
def baseEnd_2770963 : Nat := 158092877202727480913231

theorem tailTrace_2770963 : CollatzResearch.WordTrace tailWord_2770963 prefixEnd_2770963 158092877202727480913231 := by
  unfold tailWord_2770963
  simp only [CollatzResearch.WordTrace]
  refine ⟨101065323460281768648725543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67376882306854512432483695 101065323460281768648725543)
  ·
    refine ⟨151597985190422652973088315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101065323460281768648725543 151597985190422652973088315)
    ·
      refine ⟨227396977785633979459632473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151597985190422652973088315 227396977785633979459632473)
      ·
        refine ⟨170547733339225484594724355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227396977785633979459632473 170547733339225484594724355)
        ·
          refine ⟨255821600008838226892086533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170547733339225484594724355 255821600008838226892086533)
          ·
            refine ⟨47966550001657167542266225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 255821600008838226892086533 47966550001657167542266225)
            ·
              refine ⟨35974912501242875656699669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47966550001657167542266225 35974912501242875656699669)
              ·
                refine ⟨1686324023495759796407797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35974912501242875656699669 1686324023495759796407797)
                ·
                  refine ⟨158092877202727480913231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1686324023495759796407797 158092877202727480913231)
                  ·
                    rfl

theorem cell23_2770963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6, 5].length) (baseStart_2770963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770963 prefixEnd_2770963 := by exact prefixLift 2770963
  have htrace : WordTrace (prefixWord ++ tailWord_2770963) baseStart_2770963 baseEnd_2770963 := by
    simpa [prefixWord, tailWord_2770963, baseEnd_2770963] using wordTrace_append hprefix tailTrace_2770963
  have hstable : (prefixWord ++ tailWord_2770963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770963).length < 2 ^ (prefixWord ++ tailWord_2770963).sum := by decide
  have hdescent : baseEnd_2770963 < baseStart_2770963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770993 : List Nat := [1, 2, 2, 3, 1, 3, 1, 3, 2, 5]
def baseStart_2770993 : Nat := 118140960795 + 2770993 * 2 ^ 59
def prefixEnd_2770993 : Nat := 4983230072969 + 3 ^ 40 * 2770993 * 2
def baseEnd_2770993 : Nat := 474283766414727403614647

theorem tailTrace_2770993 : CollatzResearch.WordTrace tailWord_2770993 prefixEnd_2770993 474283766414727403614647 := by
  unfold tailWord_2770993
  simp only [CollatzResearch.WordTrace]
  refine ⟨101066417650173083772317633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67377611766782055848211755 101066417650173083772317633)
  ·
    refine ⟨75799813237629812829238225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101066417650173083772317633 75799813237629812829238225)
    ·
      refine ⟨56849859928222359621928669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75799813237629812829238225 56849859928222359621928669)
      ·
        refine ⟨21318697473083384858223251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56849859928222359621928669 21318697473083384858223251)
        ·
          refine ⟨31978046209625077287334877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21318697473083384858223251 31978046209625077287334877)
          ·
            refine ⟨11991767328609403982750579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31978046209625077287334877 11991767328609403982750579)
            ·
              refine ⟨17987650992914105974125869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11991767328609403982750579 17987650992914105974125869)
              ·
                refine ⟨6745369122342789740297201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17987650992914105974125869 6745369122342789740297201)
                ·
                  refine ⟨5059026841757092305222901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6745369122342789740297201 5059026841757092305222901)
                  ·
                    refine ⟨474283766414727403614647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5059026841757092305222901 474283766414727403614647)
                    ·
                      rfl

theorem cell23_2770993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 5].length) (baseStart_2770993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2770993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2770993 prefixEnd_2770993 := by exact prefixLift 2770993
  have htrace : WordTrace (prefixWord ++ tailWord_2770993) baseStart_2770993 baseEnd_2770993 := by
    simpa [prefixWord, tailWord_2770993, baseEnd_2770993] using wordTrace_append hprefix tailTrace_2770993
  have hstable : (prefixWord ++ tailWord_2770993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770993).length < 2 ^ (prefixWord ++ tailWord_2770993).sum := by decide
  have hdescent : baseEnd_2770993 < baseStart_2770993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771033 : List Nat := [1, 2, 1, 2, 2, 1, 4, 2, 1, 4, 3]
def baseStart_2771033 : Nat := 118140960795 + 2771033 * 2 ^ 59
def prefixEnd_2771033 : Nat := 4983230072969 + 3 ^ 40 * 2771033 * 2
def baseEnd_2771033 : Nat := 1422871838470362054343757

theorem tailTrace_2771033 : CollatzResearch.WordTrace tailWord_2771033 prefixEnd_2771033 1422871838470362054343757 := by
  unfold tailWord_2771033
  simp only [CollatzResearch.WordTrace]
  refine ⟨101067876570028170603773753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67378584380018780402515835 101067876570028170603773753)
  ·
    refine ⟨75800907427521127952830315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101067876570028170603773753 75800907427521127952830315)
    ·
      refine ⟨113701361141281691929245473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75800907427521127952830315 113701361141281691929245473)
      ·
        refine ⟨85276020855961268946934105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113701361141281691929245473 85276020855961268946934105)
        ·
          refine ⟨63957015641970951710200579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85276020855961268946934105 63957015641970951710200579)
          ·
            refine ⟨95935523462956427565300869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63957015641970951710200579 95935523462956427565300869)
            ·
              refine ⟨17987910649304330168493913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95935523462956427565300869 17987910649304330168493913)
              ·
                refine ⟨13490932986978247626370435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17987910649304330168493913 13490932986978247626370435)
                ·
                  refine ⟨20236399480467371439555653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13490932986978247626370435 20236399480467371439555653)
                  ·
                    refine ⟨3794324902587632144916685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20236399480467371439555653 3794324902587632144916685)
                    ·
                      refine ⟨1422871838470362054343757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3794324902587632144916685 1422871838470362054343757)
                      ·
                        rfl

theorem cell23_2771033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 4, 3].length) (baseStart_2771033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771033 prefixEnd_2771033 := by exact prefixLift 2771033
  have htrace : WordTrace (prefixWord ++ tailWord_2771033) baseStart_2771033 baseEnd_2771033 := by
    simpa [prefixWord, tailWord_2771033, baseEnd_2771033] using wordTrace_append hprefix tailTrace_2771033
  have hstable : (prefixWord ++ tailWord_2771033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771033).length < 2 ^ (prefixWord ++ tailWord_2771033).sum := by decide
  have hdescent : baseEnd_2771033 < baseStart_2771033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771040 : List Nat := [2, 1, 1, 3, 2, 4, 1, 2, 3, 4]
def baseStart_2771040 : Nat := 118140960795 + 2771040 * 2 ^ 59
def prefixEnd_2771040 : Nat := 4983230072969 + 3 ^ 40 * 2771040 * 2
def baseEnd_2771040 : Nat := 474291810944981175652075

theorem tailTrace_2771040 : CollatzResearch.WordTrace tailWord_2771040 prefixEnd_2771040 474291810944981175652075 := by
  unfold tailWord_2771040
  simp only [CollatzResearch.WordTrace]
  refine ⟨50534065940501405399639287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67378754587335207199519049 50534065940501405399639287)
  ·
    refine ⟨75801098910752108099458931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50534065940501405399639287 75801098910752108099458931)
    ·
      refine ⟨113701648366128162149188397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75801098910752108099458931 113701648366128162149188397)
      ·
        refine ⟨42638118137298060805945649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113701648366128162149188397 42638118137298060805945649)
        ·
          refine ⟨31978588602973545604459237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42638118137298060805945649 31978588602973545604459237)
          ·
            refine ⟨5995985363057539800836107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31978588602973545604459237 5995985363057539800836107)
            ·
              refine ⟨8993978044586309701254161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5995985363057539800836107 8993978044586309701254161)
              ·
                refine ⟨6745483533439732275940621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8993978044586309701254161 6745483533439732275940621)
                ·
                  refine ⟨2529556325039899603477733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6745483533439732275940621 2529556325039899603477733)
                  ·
                    refine ⟨474291810944981175652075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2529556325039899603477733 474291810944981175652075)
                    ·
                      rfl

theorem cell23_2771040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 3, 4].length) (baseStart_2771040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771040 prefixEnd_2771040 := by exact prefixLift 2771040
  have htrace : WordTrace (prefixWord ++ tailWord_2771040) baseStart_2771040 baseEnd_2771040 := by
    simpa [prefixWord, tailWord_2771040, baseEnd_2771040] using wordTrace_append hprefix tailTrace_2771040
  have hstable : (prefixWord ++ tailWord_2771040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771040).length < 2 ^ (prefixWord ++ tailWord_2771040).sum := by decide
  have hdescent : baseEnd_2771040 < baseStart_2771040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771053 : List Nat := [1, 5, 1, 1, 2, 1, 2, 2, 8]
def baseStart_2771053 : Nat := 118140960795 + 2771053 * 2 ^ 59
def prefixEnd_2771053 : Nat := 4983230072969 + 3 ^ 40 * 2771053 * 2
def baseEnd_2771053 : Nat := 158098012009272441788185

theorem tailTrace_2771053 : CollatzResearch.WordTrace tailWord_2771053 prefixEnd_2771053 158098012009272441788185 := by
  unfold tailWord_2771053
  simp only [CollatzResearch.WordTrace]
  refine ⟨101068606029955714019501813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67379070686637142679667875 101068606029955714019501813)
  ·
    refine ⟨9475181815308348189328295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101068606029955714019501813 9475181815308348189328295)
    ·
      refine ⟨14212772722962522283992443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9475181815308348189328295 14212772722962522283992443)
      ·
        refine ⟨21319159084443783425988665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14212772722962522283992443 21319159084443783425988665)
        ·
          refine ⟨15989369313332837569491499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21319159084443783425988665 15989369313332837569491499)
          ·
            refine ⟨23984053969999256354237249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15989369313332837569491499 23984053969999256354237249)
            ·
              refine ⟨17988040477499442265677937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23984053969999256354237249 17988040477499442265677937)
              ·
                refine ⟨13491030358124581699258453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17988040477499442265677937 13491030358124581699258453)
                ·
                  refine ⟨158098012009272441788185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13491030358124581699258453 158098012009272441788185)
                  ·
                    rfl

theorem cell23_2771053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_2771053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771053 prefixEnd_2771053 := by exact prefixLift 2771053
  have htrace : WordTrace (prefixWord ++ tailWord_2771053) baseStart_2771053 baseEnd_2771053 := by
    simpa [prefixWord, tailWord_2771053, baseEnd_2771053] using wordTrace_append hprefix tailTrace_2771053
  have hstable : (prefixWord ++ tailWord_2771053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771053).length < 2 ^ (prefixWord ++ tailWord_2771053).sum := by decide
  have hdescent : baseEnd_2771053 < baseStart_2771053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771057 : List Nat := [1, 2, 2, 2, 1, 1, 6, 3, 1, 4]
def baseStart_2771057 : Nat := 118140960795 + 2771057 * 2 ^ 59
def prefixEnd_2771057 : Nat := 4983230072969 + 3 ^ 40 * 2771057 * 2
def baseEnd_2771057 : Nat := 474294720668689986814549

theorem tailTrace_2771057 : CollatzResearch.WordTrace tailWord_2771057 prefixEnd_2771057 474294720668689986814549 := by
  unfold tailWord_2771057
  simp only [CollatzResearch.WordTrace]
  refine ⟨101068751921941222702647425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67379167947960815135098283 101068751921941222702647425)
  ·
    refine ⟨75801563941455917026985569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101068751921941222702647425 75801563941455917026985569)
    ·
      refine ⟨56851172956091937770239177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75801563941455917026985569 56851172956091937770239177)
      ·
        refine ⟨42638379717068953327679383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56851172956091937770239177 42638379717068953327679383)
        ·
          refine ⟨63957569575603429991519075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42638379717068953327679383 63957569575603429991519075)
          ·
            refine ⟨95936354363405144987278613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63957569575603429991519075 95936354363405144987278613)
            ·
              refine ⟨4497016610784616171278685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 95936354363405144987278613 4497016610784616171278685)
              ·
                refine ⟨1686381229044231064229507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4497016610784616171278685 1686381229044231064229507)
                ·
                  refine ⟨2529571843566346596344261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1686381229044231064229507 2529571843566346596344261)
                  ·
                    refine ⟨474294720668689986814549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2529571843566346596344261 474294720668689986814549)
                    ·
                      rfl

theorem cell23_2771057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3, 1, 4].length) (baseStart_2771057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771057 prefixEnd_2771057 := by exact prefixLift 2771057
  have htrace : WordTrace (prefixWord ++ tailWord_2771057) baseStart_2771057 baseEnd_2771057 := by
    simpa [prefixWord, tailWord_2771057, baseEnd_2771057] using wordTrace_append hprefix tailTrace_2771057
  have hstable : (prefixWord ++ tailWord_2771057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771057).length < 2 ^ (prefixWord ++ tailWord_2771057).sum := by decide
  have hdescent : baseEnd_2771057 < baseStart_2771057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771117 : List Nat := [1, 5, 2, 1, 2, 1, 2, 3, 1, 5]
def baseStart_2771117 : Nat := 118140960795 + 2771117 * 2 ^ 59
def prefixEnd_2771117 : Nat := 4983230072969 + 3 ^ 40 * 2771117 * 2
def baseEnd_2771117 : Nat := 474304990281779908564457

theorem tailTrace_2771117 : CollatzResearch.WordTrace tailWord_2771117 prefixEnd_2771117 474304990281779908564457 := by
  unfold tailWord_2771117
  simp only [CollatzResearch.WordTrace]
  refine ⟨101070940301723852949831605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67380626867815901966554403 101070940301723852949831605)
  ·
    refine ⟨9475400653286611214046713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101070940301723852949831605 9475400653286611214046713)
    ·
      refine ⟨7106550489964958410535035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9475400653286611214046713 7106550489964958410535035)
      ·
        refine ⟨10659825734947437615802553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7106550489964958410535035 10659825734947437615802553)
        ·
          refine ⟨7994869301210578211851915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10659825734947437615802553 7994869301210578211851915)
          ·
            refine ⟨11992303951815867317777873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7994869301210578211851915 11992303951815867317777873)
            ·
              refine ⟨8994227963861900488333405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11992303951815867317777873 8994227963861900488333405)
              ·
                refine ⟨3372835486448212683125027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8994227963861900488333405 3372835486448212683125027)
                ·
                  refine ⟨5059253229672319024687541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3372835486448212683125027 5059253229672319024687541)
                  ·
                    refine ⟨474304990281779908564457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5059253229672319024687541 474304990281779908564457)
                    ·
                      rfl

theorem cell23_2771117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_2771117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771117 prefixEnd_2771117 := by exact prefixLift 2771117
  have htrace : WordTrace (prefixWord ++ tailWord_2771117) baseStart_2771117 baseEnd_2771117 := by
    simpa [prefixWord, tailWord_2771117, baseEnd_2771117] using wordTrace_append hprefix tailTrace_2771117
  have hstable : (prefixWord ++ tailWord_2771117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771117).length < 2 ^ (prefixWord ++ tailWord_2771117).sum := by decide
  have hdescent : baseEnd_2771117 < baseStart_2771117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771130 : List Nat := [3, 1, 1, 1, 2, 2, 4, 1, 4, 4]
def baseStart_2771130 : Nat := 118140960795 + 2771130 * 2 ^ 59
def prefixEnd_2771130 : Nat := 4983230072969 + 3 ^ 40 * 2771130 * 2
def baseEnd_2771130 : Nat := 474307215364616058276937

theorem tailTrace_2771130 : CollatzResearch.WordTrace tailWord_2771130 prefixEnd_2771130 474307215364616058276937 := by
  unfold tailWord_2771130
  simp only [CollatzResearch.WordTrace]
  refine ⟨25267853612669189042513711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67380942967117837446703229 25267853612669189042513711)
  ·
    refine ⟨37901780419003783563770567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25267853612669189042513711 37901780419003783563770567)
    ·
      refine ⟨56852670628505675345655851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37901780419003783563770567 56852670628505675345655851)
      ·
        refine ⟨85279005942758513018483777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56852670628505675345655851 85279005942758513018483777)
        ·
          refine ⟨63959254457068884763862833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85279005942758513018483777 63959254457068884763862833)
          ·
            refine ⟨47969440842801663572897125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63959254457068884763862833 47969440842801663572897125)
            ·
              refine ⟨8994270158025311919918211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47969440842801663572897125 8994270158025311919918211)
              ·
                refine ⟨13491405237037967879877317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8994270158025311919918211 13491405237037967879877317)
                ·
                  refine ⟨2529638481944618977476997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13491405237037967879877317 2529638481944618977476997)
                  ·
                    refine ⟨474307215364616058276937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2529638481944618977476997 474307215364616058276937)
                    ·
                      rfl

theorem cell23_2771130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 4, 4].length) (baseStart_2771130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771130 prefixEnd_2771130 := by exact prefixLift 2771130
  have htrace : WordTrace (prefixWord ++ tailWord_2771130) baseStart_2771130 baseEnd_2771130 := by
    simpa [prefixWord, tailWord_2771130, baseEnd_2771130] using wordTrace_append hprefix tailTrace_2771130
  have hstable : (prefixWord ++ tailWord_2771130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771130).length < 2 ^ (prefixWord ++ tailWord_2771130).sum := by decide
  have hdescent : baseEnd_2771130 < baseStart_2771130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771150 : List Nat := [4, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6]
def baseStart_2771150 : Nat := 118140960795 + 2771150 * 2 ^ 59
def prefixEnd_2771150 : Nat := 4983230072969 + 3 ^ 40 * 2771150 * 2
def baseEnd_2771150 : Nat := 1422931915706938096580719

theorem tailTrace_2771150 : CollatzResearch.WordTrace tailWord_2771150 prefixEnd_2771150 1422931915706938096580719 := by
  unfold tailWord_2771150
  simp only [CollatzResearch.WordTrace]
  refine ⟨12634017988825537448222863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67381429273736199723855269 12634017988825537448222863)
  ·
    refine ⟨18951026983238306172334295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12634017988825537448222863 18951026983238306172334295)
    ·
      refine ⟨28426540474857459258501443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18951026983238306172334295 28426540474857459258501443)
      ·
        refine ⟨42639810712286188887752165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28426540474857459258501443 42639810712286188887752165)
        ·
          refine ⟨7994964508553660416453531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42639810712286188887752165 7994964508553660416453531)
          ·
            refine ⟨11992446762830490624680297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7994964508553660416453531 11992446762830490624680297)
            ·
              refine ⟨8994335072122867968510223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11992446762830490624680297 8994335072122867968510223)
              ·
                refine ⟨13491502608184301952765335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8994335072122867968510223 13491502608184301952765335)
                ·
                  refine ⟨20237253912276452929148003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13491502608184301952765335 20237253912276452929148003)
                  ·
                    refine ⟨30355880868414679393722005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20237253912276452929148003 30355880868414679393722005)
                    ·
                      refine ⟨1422931915706938096580719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30355880868414679393722005 1422931915706938096580719)
                      ·
                        rfl

theorem cell23_2771150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_2771150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771150 prefixEnd_2771150 := by exact prefixLift 2771150
  have htrace : WordTrace (prefixWord ++ tailWord_2771150) baseStart_2771150 baseEnd_2771150 := by
    simpa [prefixWord, tailWord_2771150, baseEnd_2771150] using wordTrace_append hprefix tailTrace_2771150
  have hstable : (prefixWord ++ tailWord_2771150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771150).length < 2 ^ (prefixWord ++ tailWord_2771150).sum := by decide
  have hdescent : baseEnd_2771150 < baseStart_2771150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771154 : List Nat := [3, 2, 2, 2, 1, 4, 1, 2, 1, 1, 4]
def baseStart_2771154 : Nat := 118140960795 + 2771154 * 2 ^ 59
def prefixEnd_2771154 : Nat := 4983230072969 + 3 ^ 40 * 2771154 * 2
def baseEnd_2771154 : Nat := 1422933969629556080930701

theorem tailTrace_2771154 : CollatzResearch.WordTrace tailWord_2771154 prefixEnd_2771154 1422933969629556080930701 := by
  unfold tailWord_2771154
  simp only [CollatzResearch.WordTrace]
  refine ⟨25268072450647452067232129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67381526535059872179285677 25268072450647452067232129)
  ·
    refine ⟨18951054337985589050424097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25268072450647452067232129 18951054337985589050424097)
    ·
      refine ⟨14213290753489191787818073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18951054337985589050424097 14213290753489191787818073)
      ·
        refine ⟨10659968065116893840863555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14213290753489191787818073 10659968065116893840863555)
        ·
          refine ⟨15989952097675340761295333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10659968065116893840863555 15989952097675340761295333)
          ·
            refine ⟨2998116018314126392742875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15989952097675340761295333 2998116018314126392742875)
            ·
              refine ⟨4497174027471189589114313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2998116018314126392742875 4497174027471189589114313)
              ·
                refine ⟨3372880520603392191835735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4497174027471189589114313 3372880520603392191835735)
                ·
                  refine ⟨5059320780905088287753603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3372880520603392191835735 5059320780905088287753603)
                  ·
                    refine ⟨7588981171357632431630405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5059320780905088287753603 7588981171357632431630405)
                    ·
                      refine ⟨1422933969629556080930701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7588981171357632431630405 1422933969629556080930701)
                      ·
                        rfl

theorem cell23_2771154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_2771154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771154 prefixEnd_2771154 := by exact prefixLift 2771154
  have htrace : WordTrace (prefixWord ++ tailWord_2771154) baseStart_2771154 baseEnd_2771154 := by
    simpa [prefixWord, tailWord_2771154, baseEnd_2771154] using wordTrace_append hprefix tailTrace_2771154
  have hstable : (prefixWord ++ tailWord_2771154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771154).length < 2 ^ (prefixWord ++ tailWord_2771154).sum := by decide
  have hdescent : baseEnd_2771154 < baseStart_2771154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771164 : List Nat := [2, 2, 5, 2, 1, 1, 1, 2, 1, 6]
def baseStart_2771164 : Nat := 118140960795 + 2771164 * 2 ^ 59
def prefixEnd_2771164 : Nat := 4983230072969 + 3 ^ 40 * 2771164 * 2
def baseEnd_2771164 : Nat := 474313034812033680601885

theorem tailTrace_2771164 : CollatzResearch.WordTrace tailWord_2771164 prefixEnd_2771164 474313034812033680601885 := by
  unfold tailWord_2771164
  simp only [CollatzResearch.WordTrace]
  refine ⟨50536327266276789988396273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67381769688369053317861697 50536327266276789988396273)
  ·
    refine ⟨37902245449707592491297205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50536327266276789988396273 37902245449707592491297205)
    ·
      refine ⟨3553335510910086796059113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37902245449707592491297205 3553335510910086796059113)
      ·
        refine ⟨2665001633182565097044335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3553335510910086796059113 2665001633182565097044335)
        ·
          refine ⟨3997502449773847645566503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2665001633182565097044335 3997502449773847645566503)
          ·
            refine ⟨5996253674660771468349755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3997502449773847645566503 5996253674660771468349755)
            ·
              refine ⟨8994380511991157202524633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5996253674660771468349755 8994380511991157202524633)
              ·
                refine ⟨6745785383993367901893475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8994380511991157202524633 6745785383993367901893475)
                ·
                  refine ⟨10118678075990051852840213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6745785383993367901893475 10118678075990051852840213)
                  ·
                    refine ⟨474313034812033680601885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10118678075990051852840213 474313034812033680601885)
                    ·
                      rfl

theorem cell23_2771164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_2771164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771164 prefixEnd_2771164 := by exact prefixLift 2771164
  have htrace : WordTrace (prefixWord ++ tailWord_2771164) baseStart_2771164 baseEnd_2771164 := by
    simpa [prefixWord, tailWord_2771164, baseEnd_2771164] using wordTrace_append hprefix tailTrace_2771164
  have hstable : (prefixWord ++ tailWord_2771164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771164).length < 2 ^ (prefixWord ++ tailWord_2771164).sum := by decide
  have hdescent : baseEnd_2771164 < baseStart_2771164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771171 : List Nat := [1, 1, 1, 8, 1, 1, 3, 1, 1, 1, 4]
def baseStart_2771171 : Nat := 118140960795 + 2771171 * 2 ^ 59
def prefixEnd_2771171 : Nat := 4983230072969 + 3 ^ 40 * 2771171 * 2
def baseEnd_2771171 : Nat := 1422942698800682514418123

theorem tailTrace_2771171 : CollatzResearch.WordTrace tailWord_2771171 prefixEnd_2771171 1422942698800682514418123 := by
  unfold tailWord_2771171
  simp only [CollatzResearch.WordTrace]
  refine ⟨101072909843528220172297367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67381939895685480114864911 101072909843528220172297367)
  ·
    refine ⟨151609364765292330258446051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101072909843528220172297367 151609364765292330258446051)
    ·
      refine ⟨227414047147938495387669077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151609364765292330258446051 227414047147938495387669077)
      ·
        refine ⟨2665008365014904242824247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 227414047147938495387669077 2665008365014904242824247)
        ·
          refine ⟨3997512547522356364236371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2665008365014904242824247 3997512547522356364236371)
          ·
            refine ⟨5996268821283534546354557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3997512547522356364236371 5996268821283534546354557)
            ·
              refine ⟨2248600807981325454882959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5996268821283534546354557 2248600807981325454882959)
              ·
                refine ⟨3372901211971988182324439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2248600807981325454882959 3372901211971988182324439)
                ·
                  refine ⟨5059351817957982273486659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3372901211971988182324439 5059351817957982273486659)
                  ·
                    refine ⟨7589027726936973410229989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5059351817957982273486659 7589027726936973410229989)
                    ·
                      refine ⟨1422942698800682514418123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7589027726936973410229989 1422942698800682514418123)
                      ·
                        rfl

theorem cell23_2771171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_2771171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771171 prefixEnd_2771171 := by exact prefixLift 2771171
  have htrace : WordTrace (prefixWord ++ tailWord_2771171) baseStart_2771171 baseEnd_2771171 := by
    simpa [prefixWord, tailWord_2771171, baseEnd_2771171] using wordTrace_append hprefix tailTrace_2771171
  have hstable : (prefixWord ++ tailWord_2771171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771171).length < 2 ^ (prefixWord ++ tailWord_2771171).sum := by decide
  have hdescent : baseEnd_2771171 < baseStart_2771171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771190 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 2, 7]
def baseStart_2771190 : Nat := 118140960795 + 2771190 * 2 ^ 59
def prefixEnd_2771190 : Nat := 4983230072969 + 3 ^ 40 * 2771190 * 2
def baseEnd_2771190 : Nat := 474317484977705980026845

theorem tailTrace_2771190 : CollatzResearch.WordTrace tailWord_2771190 prefixEnd_2771190 474317484977705980026845 := by
  unfold tailWord_2771190
  simp only [CollatzResearch.WordTrace]
  refine ⟨6317100176903711651077439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67382401886972924278159349 6317100176903711651077439)
  ·
    refine ⟨9475650265355567476616159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6317100176903711651077439 9475650265355567476616159)
    ·
      refine ⟨14213475398033351214924239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9475650265355567476616159 14213475398033351214924239)
      ·
        refine ⟨21320213097050026822386359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14213475398033351214924239 21320213097050026822386359)
        ·
          refine ⟨31980319645575040233579539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21320213097050026822386359 31980319645575040233579539)
          ·
            refine ⟨47970479468362560350369309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31980319645575040233579539 47970479468362560350369309)
            ·
              refine ⟨17988929800635960131388491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47970479468362560350369309 17988929800635960131388491)
              ·
                refine ⟨26983394700953940197082737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17988929800635960131388491 26983394700953940197082737)
                ·
                  refine ⟨20237546025715455147812053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26983394700953940197082737 20237546025715455147812053)
                  ·
                    refine ⟨474317484977705980026845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20237546025715455147812053 474317484977705980026845)
                    ·
                      rfl

theorem cell23_2771190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_2771190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771190 prefixEnd_2771190 := by exact prefixLift 2771190
  have htrace : WordTrace (prefixWord ++ tailWord_2771190) baseStart_2771190 baseEnd_2771190 := by
    simpa [prefixWord, tailWord_2771190, baseEnd_2771190] using wordTrace_append hprefix tailTrace_2771190
  have hstable : (prefixWord ++ tailWord_2771190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771190).length < 2 ^ (prefixWord ++ tailWord_2771190).sum := by decide
  have hdescent : baseEnd_2771190 < baseStart_2771190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771204 : List Nat := [2, 3, 2, 2, 3, 1, 2, 1, 1, 3, 3]
def baseStart_2771204 : Nat := 118140960795 + 2771204 * 2 ^ 59
def prefixEnd_2771204 : Nat := 4983230072969 + 3 ^ 40 * 2771204 * 2
def baseEnd_2771204 : Nat := 1422959643662280885305471

theorem tailTrace_2771204 : CollatzResearch.WordTrace tailWord_2771204 prefixEnd_2771204 1422959643662280885305471 := by
  unfold tailWord_2771204
  simp only [CollatzResearch.WordTrace]
  refine ⟨50537056726204333404124333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67382742301605777872165777 50537056726204333404124333)
  ·
    refine ⟨18951396272326625026546625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50537056726204333404124333 18951396272326625026546625)
    ·
      refine ⟨14213547204244968769909969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18951396272326625026546625 14213547204244968769909969)
      ·
        refine ⟨10660160403183726577432477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14213547204244968769909969 10660160403183726577432477)
        ·
          refine ⟨3997560151193897466537179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10660160403183726577432477 3997560151193897466537179)
          ·
            refine ⟨5996340226790846199805769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3997560151193897466537179 5996340226790846199805769)
            ·
              refine ⟨4497255170093134649854327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5996340226790846199805769 4497255170093134649854327)
              ·
                refine ⟨6745882755139701974781491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4497255170093134649854327 6745882755139701974781491)
                ·
                  refine ⟨10118824132709552962172237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6745882755139701974781491 10118824132709552962172237)
                  ·
                    refine ⟨3794559049766082360814589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10118824132709552962172237 3794559049766082360814589)
                    ·
                      refine ⟨1422959643662280885305471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3794559049766082360814589 1422959643662280885305471)
                      ·
                        rfl

theorem cell23_2771204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_2771204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771204 prefixEnd_2771204 := by exact prefixLift 2771204
  have htrace : WordTrace (prefixWord ++ tailWord_2771204) baseStart_2771204 baseEnd_2771204 := by
    simpa [prefixWord, tailWord_2771204, baseEnd_2771204] using wordTrace_append hprefix tailTrace_2771204
  have hstable : (prefixWord ++ tailWord_2771204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771204).length < 2 ^ (prefixWord ++ tailWord_2771204).sum := by decide
  have hdescent : baseEnd_2771204 < baseStart_2771204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771214 : List Nat := [4, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2]
def baseStart_2771214 : Nat := 118140960795 + 2771214 * 2 ^ 59
def prefixEnd_2771214 : Nat := 4983230072969 + 3 ^ 40 * 2771214 * 2
def baseEnd_2771214 : Nat := 1422964778468825846180425

theorem tailTrace_2771214 : CollatzResearch.WordTrace tailWord_2771214 prefixEnd_2771214 1422964778468825846180425 := by
  unfold tailWord_2771214
  simp only [CollatzResearch.WordTrace]
  refine ⟨12634309772796554814514087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67382985454914959010741797 12634309772796554814514087)
  ·
    refine ⟨18951464659194832221771131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12634309772796554814514087 18951464659194832221771131)
    ·
      refine ⟨28427196988792248332656697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18951464659194832221771131 28427196988792248332656697)
      ·
        refine ⟨21320397741594186249492523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28427196988792248332656697 21320397741594186249492523)
        ·
          refine ⟨31980596612391279374238785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21320397741594186249492523 31980596612391279374238785)
          ·
            refine ⟨23985447459293459530679089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31980596612391279374238785 23985447459293459530679089)
            ·
              refine ⟨17989085594470094648009317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23985447459293459530679089 17989085594470094648009317)
              ·
                refine ⟨3372953548963142746501747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17989085594470094648009317 3372953548963142746501747)
                ·
                  refine ⟨5059430323444714119752621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3372953548963142746501747 5059430323444714119752621)
                  ·
                    refine ⟨1897286371291767794907233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5059430323444714119752621 1897286371291767794907233)
                    ·
                      refine ⟨1422964778468825846180425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1897286371291767794907233 1422964778468825846180425)
                      ·
                        rfl

theorem cell23_2771214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_2771214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771214 prefixEnd_2771214 := by exact prefixLift 2771214
  have htrace : WordTrace (prefixWord ++ tailWord_2771214) baseStart_2771214 baseEnd_2771214 := by
    simpa [prefixWord, tailWord_2771214, baseEnd_2771214] using wordTrace_append hprefix tailTrace_2771214
  have hstable : (prefixWord ++ tailWord_2771214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771214).length < 2 ^ (prefixWord ++ tailWord_2771214).sum := by decide
  have hdescent : baseEnd_2771214 < baseStart_2771214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771227 : List Nat := [1, 1, 1, 1, 1, 1, 8, 2, 1, 4, 2]
def baseStart_2771227 : Nat := 118140960795 + 2771227 * 2 ^ 59
def prefixEnd_2771227 : Nat := 4983230072969 + 3 ^ 40 * 2771227 * 2
def baseEnd_2771227 : Nat := 1422971453717334295317865

theorem tailTrace_2771227 : CollatzResearch.WordTrace tailWord_2771227 prefixEnd_2771227 1422971453717334295317865 := by
  unfold tailWord_2771227
  simp only [CollatzResearch.WordTrace]
  refine ⟨101074952331325341736335935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67383301554216894490890623 101074952331325341736335935)
  ·
    refine ⟨151612428496988012604503903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101074952331325341736335935 151612428496988012604503903)
    ·
      refine ⟨227418642745482018906755855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151612428496988012604503903 227418642745482018906755855)
      ·
        refine ⟨341127964118223028360133783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227418642745482018906755855 341127964118223028360133783)
        ·
          refine ⟨511691946177334542540200675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341127964118223028360133783 511691946177334542540200675)
          ·
            refine ⟨767537919266001813810301013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511691946177334542540200675 767537919266001813810301013)
            ·
              refine ⟨8994584991398458755589465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 767537919266001813810301013 8994584991398458755589465)
              ·
                refine ⟨6745938743548844066692099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8994584991398458755589465 6745938743548844066692099)
                ·
                  refine ⟨10118908115323266100038149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6745938743548844066692099 10118908115323266100038149)
                  ·
                    refine ⟨1897295271623112393757153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10118908115323266100038149 1897295271623112393757153)
                    ·
                      refine ⟨1422971453717334295317865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1897295271623112393757153 1422971453717334295317865)
                      ·
                        rfl

theorem cell23_2771227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 4, 2].length) (baseStart_2771227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771227 prefixEnd_2771227 := by exact prefixLift 2771227
  have htrace : WordTrace (prefixWord ++ tailWord_2771227) baseStart_2771227 baseEnd_2771227 := by
    simpa [prefixWord, tailWord_2771227, baseEnd_2771227] using wordTrace_append hprefix tailTrace_2771227
  have hstable : (prefixWord ++ tailWord_2771227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771227).length < 2 ^ (prefixWord ++ tailWord_2771227).sum := by decide
  have hdescent : baseEnd_2771227 < baseStart_2771227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771231 : List Nat := [1, 1, 2, 4, 3, 1, 4, 1, 1, 3, 2]
def baseStart_2771231 : Nat := 118140960795 + 2771231 * 2 ^ 59
def prefixEnd_2771231 : Nat := 4983230072969 + 3 ^ 40 * 2771231 * 2
def baseEnd_2771231 : Nat := 1422973507639952279667847

theorem tailTrace_2771231 : CollatzResearch.WordTrace tailWord_2771231 prefixEnd_2771231 1422973507639952279667847 := by
  unfold tailWord_2771231
  simp only [CollatzResearch.WordTrace]
  refine ⟨101075098223310850419481547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67383398815540566946321031 101075098223310850419481547)
  ·
    refine ⟨151612647334966275629222321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101075098223310850419481547 151612647334966275629222321)
    ·
      refine ⟨113709485501224706721916741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151612647334966275629222321 113709485501224706721916741)
      ·
        refine ⟨21320528531479632510359389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113709485501224706721916741 21320528531479632510359389)
        ·
          refine ⟨7995198199304862191384771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21320528531479632510359389 7995198199304862191384771)
          ·
            refine ⟨11992797298957293287077157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7995198199304862191384771 11992797298957293287077157)
            ·
              refine ⟨2248649493554492491326967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11992797298957293287077157 2248649493554492491326967)
              ·
                refine ⟨3372974240331738736990451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2248649493554492491326967 3372974240331738736990451)
                ·
                  refine ⟨5059461360497608105485677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3372974240331738736990451 5059461360497608105485677)
                  ·
                    refine ⟨1897298010186603039557129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5059461360497608105485677 1897298010186603039557129)
                    ·
                      refine ⟨1422973507639952279667847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1897298010186603039557129 1422973507639952279667847)
                      ·
                        rfl

theorem cell23_2771231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_2771231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771231 prefixEnd_2771231 := by exact prefixLift 2771231
  have htrace : WordTrace (prefixWord ++ tailWord_2771231) baseStart_2771231 baseEnd_2771231 := by
    simpa [prefixWord, tailWord_2771231, baseEnd_2771231] using wordTrace_append hprefix tailTrace_2771231
  have hstable : (prefixWord ++ tailWord_2771231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771231).length < 2 ^ (prefixWord ++ tailWord_2771231).sum := by decide
  have hdescent : baseEnd_2771231 < baseStart_2771231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771257 : List Nat := [1, 2, 1, 6, 1, 1, 2, 1, 2, 2, 4]
def baseStart_2771257 : Nat := 118140960795 + 2771257 * 2 ^ 59
def prefixEnd_2771257 : Nat := 4983230072969 + 3 ^ 40 * 2771257 * 2
def baseEnd_2771257 : Nat := 1422986858136969177942727

theorem tailTrace_2771257 : CollatzResearch.WordTrace tailWord_2771257 prefixEnd_2771257 1422986858136969177942727 := by
  unfold tailWord_2771257
  simp only [CollatzResearch.WordTrace]
  refine ⟨101076046521216656859928025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67384031014144437906618683 101076046521216656859928025)
  ·
    refine ⟨75807034890912492644946019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101076046521216656859928025 75807034890912492644946019)
    ·
      refine ⟨113710552336368738967419029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75807034890912492644946019 113710552336368738967419029)
      ·
        refine ⟨5330182140767284639097767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 113710552336368738967419029 5330182140767284639097767)
        ·
          refine ⟨7995273211150926958646651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5330182140767284639097767 7995273211150926958646651)
          ·
            refine ⟨11992909816726390437969977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7995273211150926958646651 11992909816726390437969977)
            ·
              refine ⟨8994682362544792828477483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11992909816726390437969977 8994682362544792828477483)
              ·
                refine ⟨13492023543817189242716225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8994682362544792828477483 13492023543817189242716225)
                ·
                  refine ⟨10119017657862891932037169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13492023543817189242716225 10119017657862891932037169)
                  ·
                    refine ⟨7589263243397168949027877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10119017657862891932037169 7589263243397168949027877)
                    ·
                      refine ⟨1422986858136969177942727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7589263243397168949027877 1422986858136969177942727)
                      ·
                        rfl

theorem cell23_2771257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_2771257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771257 prefixEnd_2771257 := by exact prefixLift 2771257
  have htrace : WordTrace (prefixWord ++ tailWord_2771257) baseStart_2771257 baseEnd_2771257 := by
    simpa [prefixWord, tailWord_2771257, baseEnd_2771257] using wordTrace_append hprefix tailTrace_2771257
  have hstable : (prefixWord ++ tailWord_2771257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771257).length < 2 ^ (prefixWord ++ tailWord_2771257).sum := by decide
  have hdescent : baseEnd_2771257 < baseStart_2771257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771280 : List Nat := [2, 1, 1, 1, 1, 6, 2, 1, 1, 7]
def baseStart_2771280 : Nat := 118140960795 + 2771280 * 2 ^ 59
def prefixEnd_2771280 : Nat := 4983230072969 + 3 ^ 40 * 2771280 * 2
def baseEnd_2771280 : Nat := 474332889397340862651707

theorem tailTrace_2771280 : CollatzResearch.WordTrace tailWord_2771280 prefixEnd_2771280 474332889397340862651707 := by
  unfold tailWord_2771280
  simp only [CollatzResearch.WordTrace]
  refine ⟨50538442700066665894007647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67384590266755554525343529 50538442700066665894007647)
  ·
    refine ⟨75807664050099998841011471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50538442700066665894007647 75807664050099998841011471)
    ·
      refine ⟨113711496075149998261517207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75807664050099998841011471 113711496075149998261517207)
      ·
        refine ⟨170567244112724997392275811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113711496075149998261517207 170567244112724997392275811)
        ·
          refine ⟨255850866169087496088413717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170567244112724997392275811 255850866169087496088413717)
          ·
            refine ⟨11993009351675976379144393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 255850866169087496088413717 11993009351675976379144393)
            ·
              refine ⟨8994757013756982284358295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11993009351675976379144393 8994757013756982284358295)
              ·
                refine ⟨13492135520635473426537443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8994757013756982284358295 13492135520635473426537443)
                ·
                  refine ⟨20238203280953210139806165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13492135520635473426537443 20238203280953210139806165)
                  ·
                    refine ⟨474332889397340862651707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20238203280953210139806165 474332889397340862651707)
                    ·
                      rfl

theorem cell23_2771280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 1, 7].length) (baseStart_2771280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771280 prefixEnd_2771280 := by exact prefixLift 2771280
  have htrace : WordTrace (prefixWord ++ tailWord_2771280) baseStart_2771280 baseEnd_2771280 := by
    simpa [prefixWord, tailWord_2771280, baseEnd_2771280] using wordTrace_append hprefix tailTrace_2771280
  have hstable : (prefixWord ++ tailWord_2771280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771280).length < 2 ^ (prefixWord ++ tailWord_2771280).sum := by decide
  have hdescent : baseEnd_2771280 < baseStart_2771280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771284 : List Nat := [2, 4, 1, 1, 2, 2, 3, 3, 5]
def baseStart_2771284 : Nat := 118140960795 + 2771284 * 2 ^ 59
def prefixEnd_2771284 : Nat := 4983230072969 + 3 ^ 40 * 2771284 * 2
def baseEnd_2771284 : Nat := 158111191346071174700567

theorem tailTrace_2771284 : CollatzResearch.WordTrace tailWord_2771284 prefixEnd_2771284 158111191346071174700567 := by
  unfold tailWord_2771284
  simp only [CollatzResearch.WordTrace]
  refine ⟨50538515646059420235580453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67384687528079226980773937 50538515646059420235580453)
  ·
    refine ⟨9475971683636141294171335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50538515646059420235580453 9475971683636141294171335)
    ·
      refine ⟨14213957525454211941257003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9475971683636141294171335 14213957525454211941257003)
      ·
        refine ⟨21320936288181317911885505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14213957525454211941257003 21320936288181317911885505)
        ·
          refine ⟨15990702216135988433914129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21320936288181317911885505 15990702216135988433914129)
          ·
            refine ⟨11993026662101991325435597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15990702216135988433914129 11993026662101991325435597)
            ·
              refine ⟨4497384998288246747038349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11993026662101991325435597 4497384998288246747038349)
              ·
                refine ⟨1686519374358092530139381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4497384998288246747038349 1686519374358092530139381)
                ·
                  refine ⟨158111191346071174700567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1686519374358092530139381 158111191346071174700567)
                  ·
                    rfl

theorem cell23_2771284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_2771284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771284 prefixEnd_2771284 := by exact prefixLift 2771284
  have htrace : WordTrace (prefixWord ++ tailWord_2771284) baseStart_2771284 baseEnd_2771284 := by
    simpa [prefixWord, tailWord_2771284, baseEnd_2771284] using wordTrace_append hprefix tailTrace_2771284
  have hstable : (prefixWord ++ tailWord_2771284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771284).length < 2 ^ (prefixWord ++ tailWord_2771284).sum := by decide
  have hdescent : baseEnd_2771284 < baseStart_2771284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771290 : List Nat := [3, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5]
def baseStart_2771290 : Nat := 118140960795 + 2771290 * 2 ^ 59
def prefixEnd_2771290 : Nat := 4983230072969 + 3 ^ 40 * 2771290 * 2
def baseEnd_2771290 : Nat := 1423003802998567548830075

theorem tailTrace_2771290 : CollatzResearch.WordTrace tailWord_2771290 prefixEnd_2771290 1423003802998567548830075 := by
  unfold tailWord_2771290
  simp only [CollatzResearch.WordTrace]
  refine ⟨25269312532524275873969831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67384833420064735663919549 25269312532524275873969831)
  ·
    refine ⟨37903968798786413810954747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25269312532524275873969831 37903968798786413810954747)
    ·
      refine ⟨56855953198179620716432121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37903968798786413810954747 56855953198179620716432121)
      ·
        refine ⟨42641964898634715537324091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56855953198179620716432121 42641964898634715537324091)
        ·
          refine ⟨63962947347952073305986137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42641964898634715537324091 63962947347952073305986137)
          ·
            refine ⟨47972210510964054979489603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63962947347952073305986137 47972210510964054979489603)
            ·
              refine ⟨71958315766446082469234405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47972210510964054979489603 71958315766446082469234405)
              ·
                refine ⟨13492184206208640462981451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71958315766446082469234405 13492184206208640462981451)
                ·
                  refine ⟨20238276309312960694472177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13492184206208640462981451 20238276309312960694472177)
                  ·
                    refine ⟨15178707231984720520854133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20238276309312960694472177 15178707231984720520854133)
                    ·
                      refine ⟨1423003802998567548830075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15178707231984720520854133 1423003802998567548830075)
                      ·
                        rfl

theorem cell23_2771290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_2771290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771290 prefixEnd_2771290 := by exact prefixLift 2771290
  have htrace : WordTrace (prefixWord ++ tailWord_2771290) baseStart_2771290 baseEnd_2771290 := by
    simpa [prefixWord, tailWord_2771290, baseEnd_2771290] using wordTrace_append hprefix tailTrace_2771290
  have hstable : (prefixWord ++ tailWord_2771290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771290).length < 2 ^ (prefixWord ++ tailWord_2771290).sum := by decide
  have hdescent : baseEnd_2771290 < baseStart_2771290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771354 : List Nat := [3, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3]
def baseStart_2771354 : Nat := 118140960795 + 2771354 * 2 ^ 59
def prefixEnd_2771354 : Nat := 4983230072969 + 3 ^ 40 * 2771354 * 2
def baseEnd_2771354 : Nat := 1423036665760455298429781

theorem tailTrace_2771354 : CollatzResearch.WordTrace tailWord_2771354 prefixEnd_2771354 1423036665760455298429781 := by
  unfold tailWord_2771354
  simp only [CollatzResearch.WordTrace]
  refine ⟨25269896100466310606552279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67386389601243494950806077 25269896100466310606552279)
  ·
    refine ⟨37904844150699465909828419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25269896100466310606552279 37904844150699465909828419)
    ·
      refine ⟨56857266226049198864742629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37904844150699465909828419 56857266226049198864742629)
      ·
        refine ⟨10660737417384224787139243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56857266226049198864742629 10660737417384224787139243)
        ·
          refine ⟨15991106126076337180708865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10660737417384224787139243 15991106126076337180708865)
          ·
            refine ⟨11993329594557252885531649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15991106126076337180708865 11993329594557252885531649)
            ·
              refine ⟨8994997195917939664148737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11993329594557252885531649 8994997195917939664148737)
              ·
                refine ⟨6746247896938454748111553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8994997195917939664148737 6746247896938454748111553)
                ·
                  refine ⟨5059685922703841061083665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6746247896938454748111553 5059685922703841061083665)
                  ·
                    refine ⟨3794764442027880795812749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5059685922703841061083665 3794764442027880795812749)
                    ·
                      refine ⟨1423036665760455298429781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3794764442027880795812749 1423036665760455298429781)
                      ·
                        rfl

theorem cell23_2771354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_2771354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771354 prefixEnd_2771354 := by exact prefixLift 2771354
  have htrace : WordTrace (prefixWord ++ tailWord_2771354) baseStart_2771354 baseEnd_2771354 := by
    simpa [prefixWord, tailWord_2771354, baseEnd_2771354] using wordTrace_append hprefix tailTrace_2771354
  have hstable : (prefixWord ++ tailWord_2771354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771354).length < 2 ^ (prefixWord ++ tailWord_2771354).sum := by decide
  have hdescent : baseEnd_2771354 < baseStart_2771354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771401 : List Nat := [1, 2, 1, 1, 2, 1, 5, 5, 1, 1, 3]
def baseStart_2771401 : Nat := 118140960795 + 2771401 * 2 ^ 59
def prefixEnd_2771401 : Nat := 4983230072969 + 3 ^ 40 * 2771401 * 2
def baseEnd_2771401 : Nat := 1423060799351216614542065

theorem tailTrace_2771401 : CollatzResearch.WordTrace tailWord_2771401 prefixEnd_2771401 1423060799351216614542065 := by
  unfold tailWord_2771401
  simp only [CollatzResearch.WordTrace]
  refine ⟨101081298632694969453170057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67387532421796646302113371 101081298632694969453170057)
  ·
    refine ⟨75810973974521227089877543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101081298632694969453170057 75810973974521227089877543)
    ·
      refine ⟨113716460961781840634816315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75810973974521227089877543 113716460961781840634816315)
      ·
        refine ⟨170574691442672760952224473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113716460961781840634816315 170574691442672760952224473)
        ·
          refine ⟨127931018582004570714168355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170574691442672760952224473 127931018582004570714168355)
          ·
            refine ⟨191896527873006856071252533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127931018582004570714168355 191896527873006856071252533)
            ·
              refine ⟨17990299488094392756679925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 191896527873006856071252533 17990299488094392756679925)
              ·
                refine ⟨1686590577008849320938743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17990299488094392756679925 1686590577008849320938743)
                ·
                  refine ⟨2529885865513273981408115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1686590577008849320938743 2529885865513273981408115)
                  ·
                    refine ⟨3794828798269910972112173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2529885865513273981408115 3794828798269910972112173)
                    ·
                      refine ⟨1423060799351216614542065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3794828798269910972112173 1423060799351216614542065)
                      ·
                        rfl

theorem cell23_2771401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5, 1, 1, 3].length) (baseStart_2771401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771401 prefixEnd_2771401 := by exact prefixLift 2771401
  have htrace : WordTrace (prefixWord ++ tailWord_2771401) baseStart_2771401 baseEnd_2771401 := by
    simpa [prefixWord, tailWord_2771401, baseEnd_2771401] using wordTrace_append hprefix tailTrace_2771401
  have hstable : (prefixWord ++ tailWord_2771401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771401).length < 2 ^ (prefixWord ++ tailWord_2771401).sum := by decide
  have hdescent : baseEnd_2771401 < baseStart_2771401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771434 : List Nat := [3, 1, 3, 1, 3, 1, 3, 1, 1, 6]
def baseStart_2771434 : Nat := 118140960795 + 2771434 * 2 ^ 59
def prefixEnd_2771434 : Nat := 4983230072969 + 3 ^ 40 * 2771434 * 2
def baseEnd_2771434 : Nat := 474359248070938328476471

theorem tailTrace_2771434 : CollatzResearch.WordTrace tailWord_2771434 prefixEnd_2771434 474359248070938328476471 := by
  unfold tailWord_2771434
  simp only [CollatzResearch.WordTrace]
  refine ⟨25270625560393854022280339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67388334827716944059414237 25270625560393854022280339)
  ·
    refine ⟨37905938340590781033420509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25270625560393854022280339 37905938340590781033420509)
    ·
      refine ⟨14214726877721542887532691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37905938340590781033420509 14214726877721542887532691)
      ·
        refine ⟨21322090316582314331299037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14214726877721542887532691 21322090316582314331299037)
        ·
          refine ⟨7995783868718367874237139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21322090316582314331299037 7995783868718367874237139)
          ·
            refine ⟨11993675803077551811355709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7995783868718367874237139 11993675803077551811355709)
            ·
              refine ⟨4497628426154081929258391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11993675803077551811355709 4497628426154081929258391)
              ·
                refine ⟨6746442639231122893887587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4497628426154081929258391 6746442639231122893887587)
                ·
                  refine ⟨10119663958846684340831381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6746442639231122893887587 10119663958846684340831381)
                  ·
                    refine ⟨474359248070938328476471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10119663958846684340831381 474359248070938328476471)
                    ·
                      rfl

theorem cell23_2771434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_2771434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771434 prefixEnd_2771434 := by exact prefixLift 2771434
  have htrace : WordTrace (prefixWord ++ tailWord_2771434) baseStart_2771434 baseEnd_2771434 := by
    simpa [prefixWord, tailWord_2771434, baseEnd_2771434] using wordTrace_append hprefix tailTrace_2771434
  have hstable : (prefixWord ++ tailWord_2771434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771434).length < 2 ^ (prefixWord ++ tailWord_2771434).sum := by decide
  have hdescent : baseEnd_2771434 < baseStart_2771434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771441 : List Nat := [1, 2, 2, 2, 3, 1, 1, 4, 3, 2, 2]
def baseStart_2771441 : Nat := 118140960795 + 2771441 * 2 ^ 59
def prefixEnd_2771441 : Nat := 4983230072969 + 3 ^ 40 * 2771441 * 2
def baseEnd_2771441 : Nat := 1423081338577396458041881

theorem tailTrace_2771441 : CollatzResearch.WordTrace tailWord_2771441 prefixEnd_2771441 1423081338577396458041881 := by
  unfold tailWord_2771441
  simp only [CollatzResearch.WordTrace]
  refine ⟨101082757552550056284626177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67388505035033370856417451 101082757552550056284626177)
  ·
    refine ⟨75812068164412542213469633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101082757552550056284626177 75812068164412542213469633)
    ·
      refine ⟨56859051123309406660102225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75812068164412542213469633 56859051123309406660102225)
      ·
        refine ⟨42644288342482054995076669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56859051123309406660102225 42644288342482054995076669)
        ·
          refine ⟨15991608128430770623153751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42644288342482054995076669 15991608128430770623153751)
          ·
            refine ⟨23987412192646155934730627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15991608128430770623153751 23987412192646155934730627)
            ·
              refine ⟨35981118288969233902095941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23987412192646155934730627 35981118288969233902095941)
              ·
                refine ⟨6746459679181731356642989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35981118288969233902095941 6746459679181731356642989)
                ·
                  refine ⟨2529922379693149258741121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6746459679181731356642989 2529922379693149258741121)
                  ·
                    refine ⟨1897441784769861944055841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2529922379693149258741121 1897441784769861944055841)
                    ·
                      refine ⟨1423081338577396458041881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1897441784769861944055841 1423081338577396458041881)
                      ·
                        rfl

theorem cell23_2771441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3, 2, 2].length) (baseStart_2771441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771441 prefixEnd_2771441 := by exact prefixLift 2771441
  have htrace : WordTrace (prefixWord ++ tailWord_2771441) baseStart_2771441 baseEnd_2771441 := by
    simpa [prefixWord, tailWord_2771441, baseEnd_2771441] using wordTrace_append hprefix tailTrace_2771441
  have hstable : (prefixWord ++ tailWord_2771441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771441).length < 2 ^ (prefixWord ++ tailWord_2771441).sum := by decide
  have hdescent : baseEnd_2771441 < baseStart_2771441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771462 : List Nat := [6, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_2771462 : Nat := 118140960795 + 2771462 * 2 ^ 59
def prefixEnd_2771462 : Nat := 4983230072969 + 3 ^ 40 * 2771462 * 2
def baseEnd_2771462 : Nat := 1423092121671140875879285

theorem tailTrace_2771462 : CollatzResearch.WordTrace tailWord_2771462 prefixEnd_2771462 1423092121671140875879285 := by
  unfold tailWord_2771462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3158860108921061777223145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67389015656982651247427093 3158860108921061777223145)
  ·
    refine ⟨2369145081690796332917359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3158860108921061777223145 2369145081690796332917359)
    ·
      refine ⟨3553717622536194499376039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2369145081690796332917359 3553717622536194499376039)
      ·
        refine ⟨5330576433804291749064059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3553717622536194499376039 5330576433804291749064059)
        ·
          refine ⟨7995864650706437623596089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5330576433804291749064059 7995864650706437623596089)
          ·
            refine ⟨5996898488029828217697067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7995864650706437623596089 5996898488029828217697067)
            ·
              refine ⟨8995347732044742326545601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5996898488029828217697067 8995347732044742326545601)
              ·
                refine ⟨6746510799033556744909201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8995347732044742326545601 6746510799033556744909201)
                ·
                  refine ⟨5059883099275167558681901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6746510799033556744909201 5059883099275167558681901)
                  ·
                    refine ⟨1897456162228187834505713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5059883099275167558681901 1897456162228187834505713)
                    ·
                      refine ⟨1423092121671140875879285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1897456162228187834505713 1423092121671140875879285)
                      ·
                        rfl

theorem cell23_2771462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_2771462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771462 prefixEnd_2771462 := by exact prefixLift 2771462
  have htrace : WordTrace (prefixWord ++ tailWord_2771462) baseStart_2771462 baseEnd_2771462 := by
    simpa [prefixWord, tailWord_2771462, baseEnd_2771462] using wordTrace_append hprefix tailTrace_2771462
  have hstable : (prefixWord ++ tailWord_2771462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771462).length < 2 ^ (prefixWord ++ tailWord_2771462).sum := by decide
  have hdescent : baseEnd_2771462 < baseStart_2771462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771469 : List Nat := [1, 7, 1, 1, 1, 2, 3, 2, 1, 1, 3]
def baseStart_2771469 : Nat := 118140960795 + 2771469 * 2 ^ 59
def prefixEnd_2771469 : Nat := 4983230072969 + 3 ^ 40 * 2771469 * 2
def baseEnd_2771469 : Nat := 1423095716035722348491753

theorem tailTrace_2771469 : CollatzResearch.WordTrace tailWord_2771469 prefixEnd_2771469 1423095716035722348491753 := by
  unfold tailWord_2771469
  simp only [CollatzResearch.WordTrace]
  refine ⟨101083778796448617066645461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67389185864299078044430307 101083778796448617066645461)
  ·
    refine ⟨2369151065541764462499503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 101083778796448617066645461 2369151065541764462499503)
    ·
      refine ⟨3553726598312646693749255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2369151065541764462499503 3553726598312646693749255)
      ·
        refine ⟨5330589897468970040623883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3553726598312646693749255 5330589897468970040623883)
        ·
          refine ⟨7995884846203455060935825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5330589897468970040623883 7995884846203455060935825)
          ·
            refine ⟨5996913634652591295701869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7995884846203455060935825 5996913634652591295701869)
            ·
              refine ⟨2248842612994721735888201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5996913634652591295701869 2248842612994721735888201)
              ·
                refine ⟨1686631959746041301916151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2248842612994721735888201 1686631959746041301916151)
                ·
                  refine ⟨2529947939619061952874227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1686631959746041301916151 2529947939619061952874227)
                  ·
                    refine ⟨3794921909428592929311341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2529947939619061952874227 3794921909428592929311341)
                    ·
                      refine ⟨1423095716035722348491753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3794921909428592929311341 1423095716035722348491753)
                      ·
                        rfl

theorem cell23_2771469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_2771469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771469 prefixEnd_2771469 := by exact prefixLift 2771469
  have htrace : WordTrace (prefixWord ++ tailWord_2771469) baseStart_2771469 baseEnd_2771469 := by
    simpa [prefixWord, tailWord_2771469, baseEnd_2771469] using wordTrace_append hprefix tailTrace_2771469
  have hstable : (prefixWord ++ tailWord_2771469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771469).length < 2 ^ (prefixWord ++ tailWord_2771469).sum := by decide
  have hdescent : baseEnd_2771469 < baseStart_2771469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771475 : List Nat := [1, 1, 1, 2, 1, 5, 5, 2, 1, 2, 2]
def baseStart_2771475 : Nat := 118140960795 + 2771475 * 2 ^ 59
def prefixEnd_2771475 : Nat := 4983230072969 + 3 ^ 40 * 2771475 * 2
def baseEnd_2771475 : Nat := 1423098796919649325016725

theorem tailTrace_2771475 : CollatzResearch.WordTrace tailWord_2771475 prefixEnd_2771475 1423098796919649325016725 := by
  unfold tailWord_2771475
  simp only [CollatzResearch.WordTrace]
  refine ⟨101083997634426880091363879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67389331756284586727575919 101083997634426880091363879)
  ·
    refine ⟨151625996451640320137045819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101083997634426880091363879 151625996451640320137045819)
    ·
      refine ⟨227438994677460480205568729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151625996451640320137045819 227438994677460480205568729)
      ·
        refine ⟨170579246008095360154176547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227438994677460480205568729 170579246008095360154176547)
        ·
          refine ⟨255868869012143040231264821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170579246008095360154176547 255868869012143040231264821)
          ·
            refine ⟨23987706469888410021681077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 255868869012143040231264821 23987706469888410021681077)
            ·
              refine ⟨2248847481552038439532601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23987706469888410021681077 2248847481552038439532601)
              ·
                refine ⟨1686635611164028829649451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2248847481552038439532601 1686635611164028829649451)
                ·
                  refine ⟨2529953416746043244474177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1686635611164028829649451 2529953416746043244474177)
                  ·
                    refine ⟨1897465062559532433355633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2529953416746043244474177 1897465062559532433355633)
                    ·
                      refine ⟨1423098796919649325016725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1897465062559532433355633 1423098796919649325016725)
                      ·
                        rfl

theorem cell23_2771475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2, 1, 2, 2].length) (baseStart_2771475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771475 prefixEnd_2771475 := by exact prefixLift 2771475
  have htrace : WordTrace (prefixWord ++ tailWord_2771475) baseStart_2771475 baseEnd_2771475 := by
    simpa [prefixWord, tailWord_2771475, baseEnd_2771475] using wordTrace_append hprefix tailTrace_2771475
  have hstable : (prefixWord ++ tailWord_2771475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771475).length < 2 ^ (prefixWord ++ tailWord_2771475).sum := by decide
  have hdescent : baseEnd_2771475 < baseStart_2771475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771477 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 2, 7]
def baseStart_2771477 : Nat := 118140960795 + 2771477 * 2 ^ 59
def prefixEnd_2771477 : Nat := 4983230072969 + 3 ^ 40 * 2771477 * 2
def baseEnd_2771477 : Nat := 474366607960319439063905

theorem tailTrace_2771477 : CollatzResearch.WordTrace tailWord_2771477 prefixEnd_2771477 474366607960319439063905 := by
  unfold tailWord_2771477
  simp only [CollatzResearch.WordTrace]
  refine ⟨101084070580419634432936685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67389380386946422955291123 101084070580419634432936685)
  ·
    refine ⟨37906526467657362912351257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101084070580419634432936685 37906526467657362912351257)
    ·
      refine ⟨28429894850743022184263443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37906526467657362912351257 28429894850743022184263443)
      ·
        refine ⟨42644842276114533276395165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28429894850743022184263443 42644842276114533276395165)
        ·
          refine ⟨15991815853542949978648187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42644842276114533276395165 15991815853542949978648187)
          ·
            refine ⟨23987723780314424967972281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15991815853542949978648187 23987723780314424967972281)
            ·
              refine ⟨17990792835235818725979211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23987723780314424967972281 17990792835235818725979211)
              ·
                refine ⟨26986189252853728088968817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17990792835235818725979211 26986189252853728088968817)
                ·
                  refine ⟨20239641939640296066726613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26986189252853728088968817 20239641939640296066726613)
                  ·
                    refine ⟨474366607960319439063905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20239641939640296066726613 474366607960319439063905)
                    ·
                      rfl

theorem cell23_2771477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_2771477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771477 prefixEnd_2771477 := by exact prefixLift 2771477
  have htrace : WordTrace (prefixWord ++ tailWord_2771477) baseStart_2771477 baseEnd_2771477 := by
    simpa [prefixWord, tailWord_2771477, baseEnd_2771477] using wordTrace_append hprefix tailTrace_2771477
  have hstable : (prefixWord ++ tailWord_2771477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771477).length < 2 ^ (prefixWord ++ tailWord_2771477).sum := by decide
  have hdescent : baseEnd_2771477 < baseStart_2771477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771526 : List Nat := [6, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2]
def baseStart_2771526 : Nat := 118140960795 + 2771526 * 2 ^ 59
def prefixEnd_2771526 : Nat := 4983230072969 + 3 ^ 40 * 2771526 * 2
def baseEnd_2771526 : Nat := 1423124984433028625478991

theorem tailTrace_2771526 : CollatzResearch.WordTrace tailWord_2771526 prefixEnd_2771526 1423124984433028625478991 := by
  unfold tailWord_2771526
  simp only [CollatzResearch.WordTrace]
  refine ⟨3158933054913816118795951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67390571838161410534313621 3158933054913816118795951)
  ·
    refine ⟨4738399582370724178193927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3158933054913816118795951 4738399582370724178193927)
    ·
      refine ⟨7107599373556086267290891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4738399582370724178193927 7107599373556086267290891)
      ·
        refine ⟨10661399060334129400936337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7107599373556086267290891 10661399060334129400936337)
        ·
          refine ⟨7996049295250597050702253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10661399060334129400936337 7996049295250597050702253)
          ·
            refine ⟨2998518485718973894013345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7996049295250597050702253 2998518485718973894013345)
            ·
              refine ⟨2248888864289230420510009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2998518485718973894013345 2248888864289230420510009)
              ·
                refine ⟨1686666648216922815382507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2248888864289230420510009 1686666648216922815382507)
                ·
                  refine ⟨2529999972325384223073761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1686666648216922815382507 2529999972325384223073761)
                  ·
                    refine ⟨1897499979244038167305321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2529999972325384223073761 1897499979244038167305321)
                    ·
                      refine ⟨1423124984433028625478991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1897499979244038167305321 1423124984433028625478991)
                      ·
                        rfl

theorem cell23_2771526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_2771526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771526 prefixEnd_2771526 := by exact prefixLift 2771526
  have htrace : WordTrace (prefixWord ++ tailWord_2771526) baseStart_2771526 baseEnd_2771526 := by
    simpa [prefixWord, tailWord_2771526, baseEnd_2771526] using wordTrace_append hprefix tailTrace_2771526
  have hstable : (prefixWord ++ tailWord_2771526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771526).length < 2 ^ (prefixWord ++ tailWord_2771526).sum := by decide
  have hdescent : baseEnd_2771526 < baseStart_2771526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771531 : List Nat := [1, 1, 1, 1, 3, 1, 4, 3, 4, 2, 2]
def baseStart_2771531 : Nat := 118140960795 + 2771531 * 2 ^ 59
def prefixEnd_2771531 : Nat := 4983230072969 + 3 ^ 40 * 2771531 * 2
def baseEnd_2771531 : Nat := 1423127551836301105916467

theorem tailTrace_2771531 : CollatzResearch.WordTrace tailWord_2771531 prefixEnd_2771531 1423127551836301105916467 := by
  unfold tailWord_2771531
  simp only [CollatzResearch.WordTrace]
  refine ⟨101086040122224001655402447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67390693414816001103601631 101086040122224001655402447)
  ·
    refine ⟨151629060183336002483103671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101086040122224001655402447 151629060183336002483103671)
    ·
      refine ⟨227443590275004003724655507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151629060183336002483103671 227443590275004003724655507)
      ·
        refine ⟨341165385412506005586983261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227443590275004003724655507 341165385412506005586983261)
        ·
          refine ⟨127937019529689752095118723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 341165385412506005586983261 127937019529689752095118723)
          ·
            refine ⟨191905529294534628142678085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127937019529689752095118723 191905529294534628142678085)
            ·
              refine ⟨35982286742725242776752141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 191905529294534628142678085 35982286742725242776752141)
              ·
                refine ⟨13493357528521966041282053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35982286742725242776752141 13493357528521966041282053)
                ·
                  refine ⟨2530004536597868632740385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13493357528521966041282053 2530004536597868632740385)
                  ·
                    refine ⟨1897503402448401474555289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2530004536597868632740385 1897503402448401474555289)
                    ·
                      refine ⟨1423127551836301105916467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1897503402448401474555289 1423127551836301105916467)
                      ·
                        rfl

theorem cell23_2771531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4, 2, 2].length) (baseStart_2771531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771531 prefixEnd_2771531 := by exact prefixLift 2771531
  have htrace : WordTrace (prefixWord ++ tailWord_2771531) baseStart_2771531 baseEnd_2771531 := by
    simpa [prefixWord, tailWord_2771531, baseEnd_2771531] using wordTrace_append hprefix tailTrace_2771531
  have hstable : (prefixWord ++ tailWord_2771531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771531).length < 2 ^ (prefixWord ++ tailWord_2771531).sum := by decide
  have hdescent : baseEnd_2771531 < baseStart_2771531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771534 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3]
def baseStart_2771534 : Nat := 118140960795 + 2771534 * 2 ^ 59
def prefixEnd_2771534 : Nat := 4983230072969 + 3 ^ 40 * 2771534 * 2
def baseEnd_2771534 : Nat := 1423129092278264594178953

theorem tailTrace_2771534 : CollatzResearch.WordTrace tailWord_2771534 prefixEnd_2771534 1423129092278264594178953 := by
  unfold tailWord_2771534
  simp only [CollatzResearch.WordTrace]
  refine ⟨12635768692651641645970207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67390766360808755445174437 12635768692651641645970207)
  ·
    refine ⟨18953653038977462468955311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12635768692651641645970207 18953653038977462468955311)
    ·
      refine ⟨28430479558466193703432967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18953653038977462468955311 28430479558466193703432967)
      ·
        refine ⟨42645719337699290555149451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28430479558466193703432967 42645719337699290555149451)
        ·
          refine ⟨63968579006548935832724177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42645719337699290555149451 63968579006548935832724177)
          ·
            refine ⟨47976434254911701874543133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63968579006548935832724177 47976434254911701874543133)
            ·
              refine ⟨17991162845591888202953675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47976434254911701874543133 17991162845591888202953675)
              ·
                refine ⟨26986744268387832304430513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17991162845591888202953675 26986744268387832304430513)
                ·
                  refine ⟨20240058201290874228322885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26986744268387832304430513 20240058201290874228322885)
                  ·
                    refine ⟨3795010912742038917810541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20240058201290874228322885 3795010912742038917810541)
                    ·
                      refine ⟨1423129092278264594178953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3795010912742038917810541 1423129092278264594178953)
                      ·
                        rfl

theorem cell23_2771534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_2771534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771534 prefixEnd_2771534 := by exact prefixLift 2771534
  have htrace : WordTrace (prefixWord ++ tailWord_2771534) baseStart_2771534 baseEnd_2771534 := by
    simpa [prefixWord, tailWord_2771534, baseEnd_2771534] using wordTrace_append hprefix tailTrace_2771534
  have hstable : (prefixWord ++ tailWord_2771534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771534).length < 2 ^ (prefixWord ++ tailWord_2771534).sum := by decide
  have hdescent : baseEnd_2771534 < baseStart_2771534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771644 : List Nat := [2, 2, 2, 3, 1, 1, 1, 3, 8]
def baseStart_2771644 : Nat := 118140960795 + 2771644 * 2 ^ 59
def prefixEnd_2771644 : Nat := 4983230072969 + 3 ^ 40 * 2771644 * 2
def baseEnd_2771644 : Nat := 158131730572251018200383

theorem tailTrace_2771644 : CollatzResearch.WordTrace tailWord_2771644 prefixEnd_2771644 158131730572251018200383 := by
  unfold tailWord_2771644
  simp only [CollatzResearch.WordTrace]
  refine ⟨50545080785407310977132993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67393441047209747969510657 50545080785407310977132993)
  ·
    refine ⟨37908810589055483232849745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50545080785407310977132993 37908810589055483232849745)
    ·
      refine ⟨28431607941791612424637309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37908810589055483232849745 28431607941791612424637309)
      ·
        refine ⟨10661852978171854659238991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28431607941791612424637309 10661852978171854659238991)
        ·
          refine ⟨15992779467257781988858487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10661852978171854659238991 15992779467257781988858487)
          ·
            refine ⟨23989169200886672983287731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15992779467257781988858487 23989169200886672983287731)
            ·
              refine ⟨35983753801330009474931597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23989169200886672983287731 35983753801330009474931597)
              ·
                refine ⟨13493907675498753553099349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35983753801330009474931597 13493907675498753553099349)
                ·
                  refine ⟨158131730572251018200383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13493907675498753553099349 158131730572251018200383)
                  ·
                    rfl

theorem cell23_2771644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 8].length) (baseStart_2771644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771644 prefixEnd_2771644 := by exact prefixLift 2771644
  have htrace : WordTrace (prefixWord ++ tailWord_2771644) baseStart_2771644 baseEnd_2771644 := by
    simpa [prefixWord, tailWord_2771644, baseEnd_2771644] using wordTrace_append hprefix tailTrace_2771644
  have hstable : (prefixWord ++ tailWord_2771644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771644).length < 2 ^ (prefixWord ++ tailWord_2771644).sum := by decide
  have hdescent : baseEnd_2771644 < baseStart_2771644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771648 : List Nat := [2, 1, 1, 2, 4, 4, 1, 1, 3, 4]
def baseStart_2771648 : Nat := 118140960795 + 2771648 * 2 ^ 59
def prefixEnd_2771648 : Nat := 4983230072969 + 3 ^ 40 * 2771648 * 2
def baseEnd_2771648 : Nat := 474395876357625716051143

theorem tailTrace_2771648 : CollatzResearch.WordTrace tailWord_2771648 prefixEnd_2771648 474395876357625716051143 := by
  unfold tailWord_2771648
  simp only [CollatzResearch.WordTrace]
  refine ⟨50545153731400065318705799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67393538308533420424941065 50545153731400065318705799)
  ·
    refine ⟨75817730597100097978058699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50545153731400065318705799 75817730597100097978058699)
    ·
      refine ⟨113726595895650146967088049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75817730597100097978058699 113726595895650146967088049)
      ·
        refine ⟨85294946921737610225316037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113726595895650146967088049 85294946921737610225316037)
        ·
          refine ⟨15992802547825801917246757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85294946921737610225316037 15992802547825801917246757)
          ·
            refine ⟨2998650477717337859483767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15992802547825801917246757 2998650477717337859483767)
            ·
              refine ⟨4497975716576006789225651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2998650477717337859483767 4497975716576006789225651)
              ·
                refine ⟨6746963574864010183838477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4497975716576006789225651 6746963574864010183838477)
                ·
                  refine ⟨2530111340574003818939429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6746963574864010183838477 2530111340574003818939429)
                  ·
                    refine ⟨474395876357625716051143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2530111340574003818939429 474395876357625716051143)
                    ·
                      rfl

theorem cell23_2771648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 3, 4].length) (baseStart_2771648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771648 prefixEnd_2771648 := by exact prefixLift 2771648
  have htrace : WordTrace (prefixWord ++ tailWord_2771648) baseStart_2771648 baseEnd_2771648 := by
    simpa [prefixWord, tailWord_2771648, baseEnd_2771648] using wordTrace_append hprefix tailTrace_2771648
  have hstable : (prefixWord ++ tailWord_2771648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771648).length < 2 ^ (prefixWord ++ tailWord_2771648).sum := by decide
  have hdescent : baseEnd_2771648 < baseStart_2771648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771704 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 3, 6]
def baseStart_2771704 : Nat := 118140960795 + 2771704 * 2 ^ 59
def prefixEnd_2771704 : Nat := 4983230072969 + 3 ^ 40 * 2771704 * 2
def baseEnd_2771704 : Nat := 474405461329842976351057

theorem tailTrace_2771704 : CollatzResearch.WordTrace tailWord_2771704 prefixEnd_2771704 474405461329842976351057 := by
  unfold tailWord_2771704
  simp only [CollatzResearch.WordTrace]
  refine ⟨50546174975298626100725083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67394899967064834800966777 50546174975298626100725083)
  ·
    refine ⟨75819262462947939151087625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50546174975298626100725083 75819262462947939151087625)
    ·
      refine ⟨56864446847210954363315719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75819262462947939151087625 56864446847210954363315719)
      ·
        refine ⟨85296670270816431544973579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56864446847210954363315719 85296670270816431544973579)
        ·
          refine ⟨127945005406224647317460369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85296670270816431544973579 127945005406224647317460369)
          ·
            refine ⟨95958754054668485488095277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127945005406224647317460369 95958754054668485488095277)
            ·
              refine ⟨35984532770500682058035729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95958754054668485488095277 35984532770500682058035729)
              ·
                refine ⟨26988399577875511543526797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35984532770500682058035729 26988399577875511543526797)
                ·
                  refine ⟨10120649841703316828822549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26988399577875511543526797 10120649841703316828822549)
                  ·
                    refine ⟨474405461329842976351057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10120649841703316828822549 474405461329842976351057)
                    ·
                      rfl

theorem cell23_2771704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 3, 6].length) (baseStart_2771704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771704 prefixEnd_2771704 := by exact prefixLift 2771704
  have htrace : WordTrace (prefixWord ++ tailWord_2771704) baseStart_2771704 baseEnd_2771704 := by
    simpa [prefixWord, tailWord_2771704, baseEnd_2771704] using wordTrace_append hprefix tailTrace_2771704
  have hstable : (prefixWord ++ tailWord_2771704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771704).length < 2 ^ (prefixWord ++ tailWord_2771704).sum := by decide
  have hdescent : baseEnd_2771704 < baseStart_2771704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771711 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 2, 6, 2]
def baseStart_2771711 : Nat := 118140960795 + 2771711 * 2 ^ 59
def prefixEnd_2771711 : Nat := 4983230072969 + 3 ^ 40 * 2771711 * 2
def baseEnd_2771711 : Nat := 1423219978354110401665639

theorem tailTrace_2771711 : CollatzResearch.WordTrace tailWord_2771711 prefixEnd_2771711 1423219978354110401665639 := by
  unfold tailWord_2771711
  simp only [CollatzResearch.WordTrace]
  refine ⟨101092605261571892396954987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67395070174381261597969991 101092605261571892396954987)
  ·
    refine ⟨151638907892357838595432481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101092605261571892396954987 151638907892357838595432481)
    ·
      refine ⟨113729180919268378946574361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151638907892357838595432481 113729180919268378946574361)
      ·
        refine ⟨85296885689451284209930771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113729180919268378946574361 85296885689451284209930771)
        ·
          refine ⟨127945328534176926314896157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85296885689451284209930771 127945328534176926314896157)
          ·
            refine ⟨47979498200316347368086059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127945328534176926314896157 47979498200316347368086059)
            ·
              refine ⟨71969247300474521052129089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47979498200316347368086059 71969247300474521052129089)
              ·
                refine ⟨53976935475355890789096817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71969247300474521052129089 53976935475355890789096817)
                ·
                  refine ⟨40482701606516918091822613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53976935475355890789096817 40482701606516918091822613)
                  ·
                    refine ⟨1897626637805480535554185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40482701606516918091822613 1897626637805480535554185)
                    ·
                      refine ⟨1423219978354110401665639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1897626637805480535554185 1423219978354110401665639)
                      ·
                        rfl

theorem cell23_2771711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 6, 2].length) (baseStart_2771711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771711 prefixEnd_2771711 := by exact prefixLift 2771711
  have htrace : WordTrace (prefixWord ++ tailWord_2771711) baseStart_2771711 baseEnd_2771711 := by
    simpa [prefixWord, tailWord_2771711, baseEnd_2771711] using wordTrace_append hprefix tailTrace_2771711
  have hstable : (prefixWord ++ tailWord_2771711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771711).length < 2 ^ (prefixWord ++ tailWord_2771711).sum := by decide
  have hdescent : baseEnd_2771711 < baseStart_2771711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771731 : List Nat := [1, 1, 1, 2, 1, 3, 3, 3, 3, 2, 3]
def baseStart_2771731 : Nat := 118140960795 + 2771731 * 2 ^ 59
def prefixEnd_2771731 : Nat := 4983230072969 + 3 ^ 40 * 2771731 * 2
def baseEnd_2771731 : Nat := 1423230247967200323415547

theorem tailTrace_2771731 : CollatzResearch.WordTrace tailWord_2771731 prefixEnd_2771731 1423230247967200323415547 := by
  unfold tailWord_2771731
  simp only [CollatzResearch.WordTrace]
  refine ⟨101093334721499435812683047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67395556480999623875122031 101093334721499435812683047)
  ·
    refine ⟨151640002082249153719024571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101093334721499435812683047 151640002082249153719024571)
    ·
      refine ⟨227460003123373730578536857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151640002082249153719024571 227460003123373730578536857)
      ·
        refine ⟨170595002342530297933902643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227460003123373730578536857 170595002342530297933902643)
        ·
          refine ⟨255892503513795446900853965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170595002342530297933902643 255892503513795446900853965)
          ·
            refine ⟨95959688817673292587820237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255892503513795446900853965 95959688817673292587820237)
            ·
              refine ⟨35984883306627484720432589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95959688817673292587820237 35984883306627484720432589)
              ·
                refine ⟨13494331239985306770162221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35984883306627484720432589 13494331239985306770162221)
                ·
                  refine ⟨5060374214994490038810833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13494331239985306770162221 5060374214994490038810833)
                  ·
                    refine ⟨3795280661245867529108125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5060374214994490038810833 3795280661245867529108125)
                    ·
                      refine ⟨1423230247967200323415547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3795280661245867529108125 1423230247967200323415547)
                      ·
                        rfl

theorem cell23_2771731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2, 3].length) (baseStart_2771731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771731 prefixEnd_2771731 := by exact prefixLift 2771731
  have htrace : WordTrace (prefixWord ++ tailWord_2771731) baseStart_2771731 baseEnd_2771731 := by
    simpa [prefixWord, tailWord_2771731, baseEnd_2771731] using wordTrace_append hprefix tailTrace_2771731
  have hstable : (prefixWord ++ tailWord_2771731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771731).length < 2 ^ (prefixWord ++ tailWord_2771731).sum := by decide
  have hdescent : baseEnd_2771731 < baseStart_2771731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771762 : List Nat := [3, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2]
def baseStart_2771762 : Nat := 118140960795 + 2771762 * 2 ^ 59
def prefixEnd_2771762 : Nat := 4983230072969 + 3 ^ 40 * 2771762 * 2
def baseEnd_2771762 : Nat := 1423246165867489702127905

theorem tailTrace_2771762 : CollatzResearch.WordTrace tailWord_2771762 prefixEnd_2771762 1423246165867489702127905 := by
  unfold tailWord_2771762
  simp only [CollatzResearch.WordTrace]
  refine ⟨25273616346096782026765385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67396310256258085404707693 25273616346096782026765385)
  ·
    refine ⟨18955212259572586520074039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25273616346096782026765385 18955212259572586520074039)
    ·
      refine ⟨28432818389358879780111059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18955212259572586520074039 28432818389358879780111059)
      ·
        refine ⟨42649227584038319670166589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28432818389358879780111059 42649227584038319670166589)
        ·
          refine ⟨15993460344014369876312471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42649227584038319670166589 15993460344014369876312471)
          ·
            refine ⟨23990190516021554814468707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15993460344014369876312471 23990190516021554814468707)
            ·
              refine ⟨35985285774032332221703061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23990190516021554814468707 35985285774032332221703061)
              ·
                refine ⟨1686810270657765572892331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35985285774032332221703061 1686810270657765572892331)
                ·
                  refine ⟨2530215405986648359338497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1686810270657765572892331 2530215405986648359338497)
                  ·
                    refine ⟨1897661554489986269503873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2530215405986648359338497 1897661554489986269503873)
                    ·
                      refine ⟨1423246165867489702127905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1897661554489986269503873 1423246165867489702127905)
                      ·
                        rfl

theorem cell23_2771762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2].length) (baseStart_2771762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771762 prefixEnd_2771762 := by exact prefixLift 2771762
  have htrace : WordTrace (prefixWord ++ tailWord_2771762) baseStart_2771762 baseEnd_2771762 := by
    simpa [prefixWord, tailWord_2771762, baseEnd_2771762] using wordTrace_append hprefix tailTrace_2771762
  have hstable : (prefixWord ++ tailWord_2771762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771762).length < 2 ^ (prefixWord ++ tailWord_2771762).sum := by decide
  have hdescent : baseEnd_2771762 < baseStart_2771762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771796 : List Nat := [2, 4, 1, 1, 4, 2, 1, 3, 1, 2, 2]
def baseStart_2771796 : Nat := 118140960795 + 2771796 * 2 ^ 59
def prefixEnd_2771796 : Nat := 4983230072969 + 3 ^ 40 * 2771796 * 2
def baseEnd_2771796 : Nat := 1423263624209742569102749

theorem tailTrace_2771796 : CollatzResearch.WordTrace tailWord_2771796 prefixEnd_2771796 1423263624209742569102749 := by
  unfold tailWord_2771796
  simp only [CollatzResearch.WordTrace]
  refine ⟨50547852733131975956899621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67397136977509301275866161 50547852733131975956899621)
  ·
    refine ⟨9477722387462245491918679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50547852733131975956899621 9477722387462245491918679)
    ·
      refine ⟨14216583581193368237878019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9477722387462245491918679 14216583581193368237878019)
      ·
        refine ⟨21324875371790052356817029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14216583581193368237878019 21324875371790052356817029)
        ·
          refine ⟨3998414132210634816903193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21324875371790052356817029 3998414132210634816903193)
          ·
            refine ⟨2998810599157976112677395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3998414132210634816903193 2998810599157976112677395)
            ·
              refine ⟨4498215898736964169016093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2998810599157976112677395 4498215898736964169016093)
              ·
                refine ⟨1686830962026361563381035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4498215898736964169016093 1686830962026361563381035)
                ·
                  refine ⟨2530246443039542345071553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1686830962026361563381035 2530246443039542345071553)
                  ·
                    refine ⟨1897684832279656758803665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2530246443039542345071553 1897684832279656758803665)
                    ·
                      refine ⟨1423263624209742569102749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1897684832279656758803665 1423263624209742569102749)
                      ·
                        rfl

theorem cell23_2771796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_2771796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771796 prefixEnd_2771796 := by exact prefixLift 2771796
  have htrace : WordTrace (prefixWord ++ tailWord_2771796) baseStart_2771796 baseEnd_2771796 := by
    simpa [prefixWord, tailWord_2771796, baseEnd_2771796] using wordTrace_append hprefix tailTrace_2771796
  have hstable : (prefixWord ++ tailWord_2771796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771796).length < 2 ^ (prefixWord ++ tailWord_2771796).sum := by decide
  have hdescent : baseEnd_2771796 < baseStart_2771796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771821 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_2771821 : Nat := 118140960795 + 2771821 * 2 ^ 59
def prefixEnd_2771821 : Nat := 4983230072969 + 3 ^ 40 * 2771821 * 2
def baseEnd_2771821 : Nat := 1423276461226104971290133

theorem tailTrace_2771821 : CollatzResearch.WordTrace tailWord_2771821 prefixEnd_2771821 1423276461226104971290133 := by
  unfold tailWord_2771821
  simp only [CollatzResearch.WordTrace]
  refine ⟨101096617291173381183459317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67397744860782254122306211 101096617291173381183459317)
  ·
    refine ⟨9477807871047504485949311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101096617291173381183459317 9477807871047504485949311)
    ·
      refine ⟨14216711806571256728923967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9477807871047504485949311 14216711806571256728923967)
      ·
        refine ⟨21325067709856885093385951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14216711806571256728923967 21325067709856885093385951)
        ·
          refine ⟨31987601564785327640078927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21325067709856885093385951 31987601564785327640078927)
          ·
            refine ⟨47981402347177991460118391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31987601564785327640078927 47981402347177991460118391)
            ·
              refine ⟨71972103520766987190177587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47981402347177991460118391 71972103520766987190177587)
              ·
                refine ⟨107958155281150480785266381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71972103520766987190177587 107958155281150480785266381)
                ·
                  refine ⟨40484308230431430294474893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107958155281150480785266381 40484308230431430294474893)
                  ·
                    refine ⟨15181615586411786360428085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40484308230431430294474893 15181615586411786360428085)
                    ·
                      refine ⟨1423276461226104971290133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15181615586411786360428085 1423276461226104971290133)
                      ·
                        rfl

theorem cell23_2771821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_2771821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771821 prefixEnd_2771821 := by exact prefixLift 2771821
  have htrace : WordTrace (prefixWord ++ tailWord_2771821) baseStart_2771821 baseEnd_2771821 := by
    simpa [prefixWord, tailWord_2771821, baseEnd_2771821] using wordTrace_append hprefix tailTrace_2771821
  have hstable : (prefixWord ++ tailWord_2771821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771821).length < 2 ^ (prefixWord ++ tailWord_2771821).sum := by decide
  have hdescent : baseEnd_2771821 < baseStart_2771821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771829 : List Nat := [1, 3, 4, 1, 1, 4, 2, 1, 2, 1, 3]
def baseStart_2771829 : Nat := 118140960795 + 2771829 * 2 ^ 59
def prefixEnd_2771829 : Nat := 4983230072969 + 3 ^ 40 * 2771829 * 2
def baseEnd_2771829 : Nat := 1423280569071340939990097

theorem tailTrace_2771829 : CollatzResearch.WordTrace tailWord_2771829 prefixEnd_2771829 1423280569071340939990097 := by
  unfold tailWord_2771829
  simp only [CollatzResearch.WordTrace]
  refine ⟨101096909075144398549750541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67397939383429599033167027 101096909075144398549750541)
  ·
    refine ⟨37911340903179149456156453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101096909075144398549750541 37911340903179149456156453)
    ·
      refine ⟨7108376419346090523029335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37911340903179149456156453 7108376419346090523029335)
      ·
        refine ⟨10662564629019135784544003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7108376419346090523029335 10662564629019135784544003)
        ·
          refine ⟨15993846943528703676816005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10662564629019135784544003 15993846943528703676816005)
          ·
            refine ⟨2998846301911631939403001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15993846943528703676816005 2998846301911631939403001)
            ·
              refine ⟨2249134726433723954552251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2998846301911631939403001 2249134726433723954552251)
              ·
                refine ⟨3373702089650585931828377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2249134726433723954552251 3373702089650585931828377)
                ·
                  refine ⟨2530276567237939448871283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3373702089650585931828377 2530276567237939448871283)
                  ·
                    refine ⟨3795414850856909173306925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2530276567237939448871283 3795414850856909173306925)
                    ·
                      refine ⟨1423280569071340939990097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3795414850856909173306925 1423280569071340939990097)
                      ·
                        rfl

theorem cell23_2771829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_2771829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771829 prefixEnd_2771829 := by exact prefixLift 2771829
  have htrace : WordTrace (prefixWord ++ tailWord_2771829) baseStart_2771829 baseEnd_2771829 := by
    simpa [prefixWord, tailWord_2771829, baseEnd_2771829] using wordTrace_append hprefix tailTrace_2771829
  have hstable : (prefixWord ++ tailWord_2771829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771829).length < 2 ^ (prefixWord ++ tailWord_2771829).sum := by decide
  have hdescent : baseEnd_2771829 < baseStart_2771829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771831 : List Nat := [1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 4]
def baseStart_2771831 : Nat := 118140960795 + 2771831 * 2 ^ 59
def prefixEnd_2771831 : Nat := 4983230072969 + 3 ^ 40 * 2771831 * 2
def baseEnd_2771831 : Nat := 1423281596032649932165087

theorem tailTrace_2771831 : CollatzResearch.WordTrace tailWord_2771831 prefixEnd_2771831 1423281596032649932165087 := by
  unfold tailWord_2771831
  simp only [CollatzResearch.WordTrace]
  refine ⟨101096982021137152891323347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67397988014091435260882231 101096982021137152891323347)
  ·
    refine ⟨151645473031705729336985021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101096982021137152891323347 151645473031705729336985021)
    ·
      refine ⟨56867052386889648501369383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151645473031705729336985021 56867052386889648501369383)
      ·
        refine ⟨85300578580334472752054075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56867052386889648501369383 85300578580334472752054075)
        ·
          refine ⟨127950867870501709128081113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85300578580334472752054075 127950867870501709128081113)
          ·
            refine ⟨95963150902876281846060835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127950867870501709128081113 95963150902876281846060835)
            ·
              refine ⟨143944726354314422769091253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95963150902876281846060835 143944726354314422769091253)
              ·
                refine ⟨13494818095716977134602305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 143944726354314422769091253 13494818095716977134602305)
                ·
                  refine ⟨10121113571787732850951729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13494818095716977134602305 10121113571787732850951729)
                  ·
                    refine ⟨7590835178840799638213797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10121113571787732850951729 7590835178840799638213797)
                    ·
                      refine ⟨1423281596032649932165087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7590835178840799638213797 1423281596032649932165087)
                      ·
                        rfl

theorem cell23_2771831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_2771831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771831 prefixEnd_2771831 := by exact prefixLift 2771831
  have htrace : WordTrace (prefixWord ++ tailWord_2771831) baseStart_2771831 baseEnd_2771831 := by
    simpa [prefixWord, tailWord_2771831, baseEnd_2771831] using wordTrace_append hprefix tailTrace_2771831
  have hstable : (prefixWord ++ tailWord_2771831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771831).length < 2 ^ (prefixWord ++ tailWord_2771831).sum := by decide
  have hdescent : baseEnd_2771831 < baseStart_2771831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771875 : List Nat := [1, 1, 1, 4, 1, 2, 6, 2, 5]
def baseStart_2771875 : Nat := 118140960795 + 2771875 * 2 ^ 59
def prefixEnd_2771875 : Nat := 4983230072969 + 3 ^ 40 * 2771875 * 2
def baseEnd_2771875 : Nat := 158144909909049751112765

theorem tailTrace_2771875 : CollatzResearch.WordTrace tailWord_2771875 prefixEnd_2771875 158144909909049751112765 := by
  unfold tailWord_2771875
  simp only [CollatzResearch.WordTrace]
  refine ⟨101098586832977748405925079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67399057888651832270616719 101098586832977748405925079)
  ·
    refine ⟨151647880249466622608887619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101098586832977748405925079 151647880249466622608887619)
    ·
      refine ⟨227471820374199933913331429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151647880249466622608887619 227471820374199933913331429)
      ·
        refine ⟨42650966320162487608749643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 227471820374199933913331429 42650966320162487608749643)
        ·
          refine ⟨63976449480243731413124465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42650966320162487608749643 63976449480243731413124465)
          ·
            refine ⟨47982337110182798559843349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63976449480243731413124465 47982337110182798559843349)
            ·
              refine ⟨2249172052039818682492657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47982337110182798559843349 2249172052039818682492657)
              ·
                refine ⟨1686879039029864011869493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2249172052039818682492657 1686879039029864011869493)
                ·
                  refine ⟨158144909909049751112765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1686879039029864011869493 158144909909049751112765)
                  ·
                    rfl

theorem cell23_2771875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2, 5].length) (baseStart_2771875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771875 prefixEnd_2771875 := by exact prefixLift 2771875
  have htrace : WordTrace (prefixWord ++ tailWord_2771875) baseStart_2771875 baseEnd_2771875 := by
    simpa [prefixWord, tailWord_2771875, baseEnd_2771875] using wordTrace_append hprefix tailTrace_2771875
  have hstable : (prefixWord ++ tailWord_2771875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771875).length < 2 ^ (prefixWord ++ tailWord_2771875).sum := by decide
  have hdescent : baseEnd_2771875 < baseStart_2771875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771881 : List Nat := [1, 2, 1, 1, 1, 1, 5, 3, 1, 2, 5]
def baseStart_2771881 : Nat := 118140960795 + 2771881 * 2 ^ 59
def prefixEnd_2771881 : Nat := 4983230072969 + 3 ^ 40 * 2771881 * 2
def baseEnd_2771881 : Nat := 1423307270065374736539857

theorem tailTrace_2771881 : CollatzResearch.WordTrace tailWord_2771881 prefixEnd_2771881 1423307270065374736539857 := by
  unfold tailWord_2771881
  simp only [CollatzResearch.WordTrace]
  refine ⟨101098805670956011430643497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67399203780637340953762331 101098805670956011430643497)
  ·
    refine ⟨75824104253217008572982623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101098805670956011430643497 75824104253217008572982623)
    ·
      refine ⟨113736156379825512859473935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75824104253217008572982623 113736156379825512859473935)
      ·
        refine ⟨170604234569738269289210903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113736156379825512859473935 170604234569738269289210903)
        ·
          refine ⟨255906351854607403933816355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170604234569738269289210903 255906351854607403933816355)
          ·
            refine ⟨383859527781911105900724533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255906351854607403933816355 383859527781911105900724533)
            ·
              refine ⟨35986830729554166178192925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 383859527781911105900724533 35986830729554166178192925)
              ·
                refine ⟨13495061523582812316822347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35986830729554166178192925 13495061523582812316822347)
                ·
                  refine ⟨20242592285374218475233521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13495061523582812316822347 20242592285374218475233521)
                  ·
                    refine ⟨15181944214030663856425141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20242592285374218475233521 15181944214030663856425141)
                    ·
                      refine ⟨1423307270065374736539857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15181944214030663856425141 1423307270065374736539857)
                      ·
                        rfl

theorem cell23_2771881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 2, 5].length) (baseStart_2771881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771881 prefixEnd_2771881 := by exact prefixLift 2771881
  have htrace : WordTrace (prefixWord ++ tailWord_2771881) baseStart_2771881 baseEnd_2771881 := by
    simpa [prefixWord, tailWord_2771881, baseEnd_2771881] using wordTrace_append hprefix tailTrace_2771881
  have hstable : (prefixWord ++ tailWord_2771881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771881).length < 2 ^ (prefixWord ++ tailWord_2771881).sum := by decide
  have hdescent : baseEnd_2771881 < baseStart_2771881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771921 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 1, 3, 6]
def baseStart_2771921 : Nat := 118140960795 + 2771921 * 2 ^ 59
def prefixEnd_2771921 : Nat := 4983230072969 + 3 ^ 40 * 2771921 * 2
def baseEnd_2771921 : Nat := 1423327809291554580039673

theorem tailTrace_2771921 : CollatzResearch.WordTrace tailWord_2771921 prefixEnd_2771921 1423327809291554580039673 := by
  unfold tailWord_2771921
  simp only [CollatzResearch.WordTrace]
  refine ⟨101100264590811098262099617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67400176393874065508066411 101100264590811098262099617)
  ·
    refine ⟨75825198443108323696574713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101100264590811098262099617 75825198443108323696574713)
    ·
      refine ⟨56868898832331242772431035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75825198443108323696574713 56868898832331242772431035)
      ·
        refine ⟨85303348248496864158646553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56868898832331242772431035 85303348248496864158646553)
        ·
          refine ⟨63977511186372648118984915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85303348248496864158646553 63977511186372648118984915)
          ·
            refine ⟨95966266779558972178477373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63977511186372648118984915 95966266779558972178477373)
            ·
              refine ⟨35987350042334614566929015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95966266779558972178477373 35987350042334614566929015)
              ·
                refine ⟨53981025063501921850393523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35987350042334614566929015 53981025063501921850393523)
                ·
                  refine ⟨80971537595252882775590285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53981025063501921850393523 80971537595252882775590285)
                  ·
                    refine ⟨30364326598219831040846357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80971537595252882775590285 30364326598219831040846357)
                    ·
                      refine ⟨1423327809291554580039673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30364326598219831040846357 1423327809291554580039673)
                      ·
                        rfl

theorem cell23_2771921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_2771921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771921 prefixEnd_2771921 := by exact prefixLift 2771921
  have htrace : WordTrace (prefixWord ++ tailWord_2771921) baseStart_2771921 baseEnd_2771921 := by
    simpa [prefixWord, tailWord_2771921, baseEnd_2771921] using wordTrace_append hprefix tailTrace_2771921
  have hstable : (prefixWord ++ tailWord_2771921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771921).length < 2 ^ (prefixWord ++ tailWord_2771921).sum := by decide
  have hdescent : baseEnd_2771921 < baseStart_2771921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771969 : List Nat := [1, 2, 4, 1, 2, 4, 1, 3, 1, 4]
def baseStart_2771969 : Nat := 118140960795 + 2771969 * 2 ^ 59
def prefixEnd_2771969 : Nat := 4983230072969 + 3 ^ 40 * 2771969 * 2
def baseEnd_2771969 : Nat := 474450818787656797413151

theorem tailTrace_2771969 : CollatzResearch.WordTrace tailWord_2771969 prefixEnd_2771969 474450818787656797413151 := by
  unfold tailWord_2771969
  simp only [CollatzResearch.WordTrace]
  refine ⟨101102015294637202459846961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67401343529758134973231307 101102015294637202459846961)
  ·
    refine ⟨75826511470977901844885221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101102015294637202459846961 75826511470977901844885221)
    ·
      refine ⟨14217470900808356595915979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75826511470977901844885221 14217470900808356595915979)
      ·
        refine ⟨21326206351212534893873969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14217470900808356595915979 21326206351212534893873969)
        ·
          refine ⟨15994654763409401170405477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21326206351212534893873969 15994654763409401170405477)
          ·
            refine ⟨2998997768139262719451027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15994654763409401170405477 2998997768139262719451027)
            ·
              refine ⟨4498496652208894079176541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2998997768139262719451027 4498496652208894079176541)
              ·
                refine ⟨1686936244578335279691203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4498496652208894079176541 1686936244578335279691203)
                ·
                  refine ⟨2530404366867502919536805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1686936244578335279691203 2530404366867502919536805)
                  ·
                    refine ⟨474450818787656797413151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2530404366867502919536805 474450818787656797413151)
                    ·
                      rfl

theorem cell23_2771969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_2771969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771969 prefixEnd_2771969 := by exact prefixLift 2771969
  have htrace : WordTrace (prefixWord ++ tailWord_2771969) baseStart_2771969 baseEnd_2771969 := by
    simpa [prefixWord, tailWord_2771969, baseEnd_2771969] using wordTrace_append hprefix tailTrace_2771969
  have hstable : (prefixWord ++ tailWord_2771969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771969).length < 2 ^ (prefixWord ++ tailWord_2771969).sum := by decide
  have hdescent : baseEnd_2771969 < baseStart_2771969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771992 : List Nat := [2, 1, 2, 3, 2, 2, 3, 1, 3, 1, 3]
def baseStart_2771992 : Nat := 118140960795 + 2771992 * 2 ^ 59
def prefixEnd_2771992 : Nat := 4983230072969 + 3 ^ 40 * 2771992 * 2
def baseEnd_2771992 : Nat := 1423364266418023802251847

theorem tailTrace_2771992 : CollatzResearch.WordTrace tailWord_2771992 prefixEnd_2771992 1423364266418023802251847 := by
  unfold tailWord_2771992
  simp only [CollatzResearch.WordTrace]
  refine ⟨50551427086776938693967115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67401902782369251591956153 50551427086776938693967115)
  ·
    refine ⟨75827140630165408040950673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50551427086776938693967115 75827140630165408040950673)
    ·
      refine ⟨56870355472624056030713005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75827140630165408040950673 56870355472624056030713005)
      ·
        refine ⟨21326383302234021011517377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56870355472624056030713005 21326383302234021011517377)
        ·
          refine ⟨15994787476675515758638033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21326383302234021011517377 15994787476675515758638033)
          ·
            refine ⟨11996090607506636818978525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15994787476675515758638033 11996090607506636818978525)
            ·
              refine ⟨4498533977814988807116947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11996090607506636818978525 4498533977814988807116947)
              ·
                refine ⟨6747800966722483210675421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4498533977814988807116947 6747800966722483210675421)
                ·
                  refine ⟨2530425362520931204003283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6747800966722483210675421 2530425362520931204003283)
                  ·
                    refine ⟨3795638043781396806004925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2530425362520931204003283 3795638043781396806004925)
                    ·
                      refine ⟨1423364266418023802251847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3795638043781396806004925 1423364266418023802251847)
                      ·
                        rfl

theorem cell23_2771992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_2771992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2771992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2771992 prefixEnd_2771992 := by exact prefixLift 2771992
  have htrace : WordTrace (prefixWord ++ tailWord_2771992) baseStart_2771992 baseEnd_2771992 := by
    simpa [prefixWord, tailWord_2771992, baseEnd_2771992] using wordTrace_append hprefix tailTrace_2771992
  have hstable : (prefixWord ++ tailWord_2771992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771992).length < 2 ^ (prefixWord ++ tailWord_2771992).sum := by decide
  have hdescent : baseEnd_2771992 < baseStart_2771992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772025 : List Nat := [1, 2, 1, 5, 2, 2, 1, 2, 1, 6]
def baseStart_2772025 : Nat := 118140960795 + 2772025 * 2 ^ 59
def prefixEnd_2772025 : Nat := 4983230072969 + 3 ^ 40 * 2772025 * 2
def baseEnd_2772025 : Nat := 474460403759874057713065

theorem tailTrace_2772025 : CollatzResearch.WordTrace tailWord_2772025 prefixEnd_2772025 474460403759874057713065 := by
  unfold tailWord_2772025
  simp only [CollatzResearch.WordTrace]
  refine ⟨101104057782434324023885529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67402705188289549349257019 101104057782434324023885529)
  ·
    refine ⟨75828043336825743017914147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101104057782434324023885529 75828043336825743017914147)
    ·
      refine ⟨113742065005238614526871221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75828043336825743017914147 113742065005238614526871221)
      ·
        refine ⟨10663318594241120111894177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113742065005238614526871221 10663318594241120111894177)
        ·
          refine ⟨7997488945680840083920633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10663318594241120111894177 7997488945680840083920633)
          ·
            refine ⟨5998116709260630062940475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7997488945680840083920633 5998116709260630062940475)
            ·
              refine ⟨8997175063890945094410713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5998116709260630062940475 8997175063890945094410713)
              ·
                refine ⟨6747881297918208820808035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8997175063890945094410713 6747881297918208820808035)
                ·
                  refine ⟨10121821946877313231212053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6747881297918208820808035 10121821946877313231212053)
                  ·
                    refine ⟨474460403759874057713065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10121821946877313231212053 474460403759874057713065)
                    ·
                      rfl

theorem cell23_2772025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 6].length) (baseStart_2772025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772025 prefixEnd_2772025 := by exact prefixLift 2772025
  have htrace : WordTrace (prefixWord ++ tailWord_2772025) baseStart_2772025 baseEnd_2772025 := by
    simpa [prefixWord, tailWord_2772025, baseEnd_2772025] using wordTrace_append hprefix tailTrace_2772025
  have hstable : (prefixWord ++ tailWord_2772025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772025).length < 2 ^ (prefixWord ++ tailWord_2772025).sum := by decide
  have hdescent : baseEnd_2772025 < baseStart_2772025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772032 : List Nat := [2, 1, 1, 2, 2, 3, 5, 1, 1, 1, 4]
def baseStart_2772032 : Nat := 118140960795 + 2772032 * 2 ^ 59
def prefixEnd_2772032 : Nat := 4983230072969 + 3 ^ 40 * 2772032 * 2
def baseEnd_2772032 : Nat := 1423384805644203645751663

theorem tailTrace_2772032 : CollatzResearch.WordTrace tailWord_2772032 prefixEnd_2772032 1423384805644203645751663 := by
  unfold tailWord_2772032
  simp only [CollatzResearch.WordTrace]
  refine ⟨50552156546704482109695175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67402875395605976146260233 50552156546704482109695175)
  ·
    refine ⟨75828234820056723164542763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50552156546704482109695175 75828234820056723164542763)
    ·
      refine ⟨113742352230085084746814145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75828234820056723164542763 113742352230085084746814145)
      ·
        refine ⟨85306764172563813560110609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113742352230085084746814145 85306764172563813560110609)
        ·
          refine ⟨63980073129422860170082957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85306764172563813560110609 63980073129422860170082957)
          ·
            refine ⟨23992527423533572563781109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63980073129422860170082957 23992527423533572563781109)
            ·
              refine ⟨2249299445956272427854479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23992527423533572563781109 2249299445956272427854479)
              ·
                refine ⟨3373949168934408641781719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2249299445956272427854479 3373949168934408641781719)
                ·
                  refine ⟨5060923753401612962672579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3373949168934408641781719 5060923753401612962672579)
                  ·
                    refine ⟨7591385630102419444008869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5060923753401612962672579 7591385630102419444008869)
                    ·
                      refine ⟨1423384805644203645751663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7591385630102419444008869 1423384805644203645751663)
                      ·
                        rfl

theorem cell23_2772032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 1, 1, 4].length) (baseStart_2772032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772032 prefixEnd_2772032 := by exact prefixLift 2772032
  have htrace : WordTrace (prefixWord ++ tailWord_2772032) baseStart_2772032 baseEnd_2772032 := by
    simpa [prefixWord, tailWord_2772032, baseEnd_2772032] using wordTrace_append hprefix tailTrace_2772032
  have hstable : (prefixWord ++ tailWord_2772032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772032).length < 2 ^ (prefixWord ++ tailWord_2772032).sum := by decide
  have hdescent : baseEnd_2772032 < baseStart_2772032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772065 : List Nat := [1, 2, 3, 1, 1, 2, 3, 3, 1, 3, 3]
def baseStart_2772065 : Nat := 118140960795 + 2772065 * 2 ^ 59
def prefixEnd_2772065 : Nat := 4983230072969 + 3 ^ 40 * 2772065 * 2
def baseEnd_2772065 : Nat := 1423401750505802016639011

theorem tailTrace_2772065 : CollatzResearch.WordTrace tailWord_2772065 prefixEnd_2772065 1423401750505802016639011 := by
  unfold tailWord_2772065
  simp only [CollatzResearch.WordTrace]
  refine ⟨101105516702289410855341649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67403677801526273903561099 101105516702289410855341649)
  ·
    refine ⟨75829137526717058141506237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101105516702289410855341649 75829137526717058141506237)
    ·
      refine ⟨28435926572518896803064839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75829137526717058141506237 28435926572518896803064839)
      ·
        refine ⟨42653889858778345204597259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28435926572518896803064839 42653889858778345204597259)
        ·
          refine ⟨63980834788167517806895889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42653889858778345204597259 63980834788167517806895889)
          ·
            refine ⟨47985626091125638355171917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63980834788167517806895889 47985626091125638355171917)
            ·
              refine ⟨17994609784172114383189469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47985626091125638355171917 17994609784172114383189469)
              ·
                refine ⟨6747978669064542893696051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17994609784172114383189469 6747978669064542893696051)
                ·
                  refine ⟨10121968003596814340544077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6747978669064542893696051 10121968003596814340544077)
                  ·
                    refine ⟨3795738001348805377704029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10121968003596814340544077 3795738001348805377704029)
                    ·
                      refine ⟨1423401750505802016639011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3795738001348805377704029 1423401750505802016639011)
                      ·
                        rfl

theorem cell23_2772065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_2772065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772065 prefixEnd_2772065 := by exact prefixLift 2772065
  have htrace : WordTrace (prefixWord ++ tailWord_2772065) baseStart_2772065 baseEnd_2772065 := by
    simpa [prefixWord, tailWord_2772065, baseEnd_2772065] using wordTrace_append hprefix tailTrace_2772065
  have hstable : (prefixWord ++ tailWord_2772065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772065).length < 2 ^ (prefixWord ++ tailWord_2772065).sum := by decide
  have hdescent : baseEnd_2772065 < baseStart_2772065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772066 : List Nat := [3, 3, 2, 2, 1, 2, 1, 2, 3, 2, 2]
def baseStart_2772066 : Nat := 118140960795 + 2772066 * 2 ^ 59
def prefixEnd_2772066 : Nat := 4983230072969 + 3 ^ 40 * 2772066 * 2
def baseEnd_2772066 : Nat := 1423402263986456512726507

theorem tailTrace_2772066 : CollatzResearch.WordTrace tailWord_2772066 prefixEnd_2772066 1423402263986456512726507 := by
  unfold tailWord_2772066
  simp only [CollatzResearch.WordTrace]
  refine ⟨25276388293821447006532013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67403702116857192017418701 25276388293821447006532013)
  ·
    refine ⟨9478645610183042627449505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25276388293821447006532013 9478645610183042627449505)
    ·
      refine ⟨7108984207637281970587129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9478645610183042627449505 7108984207637281970587129)
      ·
        refine ⟨5331738155727961477940347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7108984207637281970587129 5331738155727961477940347)
        ·
          refine ⟨7997607233591942216910521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5331738155727961477940347 7997607233591942216910521)
          ·
            refine ⟨5998205425193956662682891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7997607233591942216910521 5998205425193956662682891)
            ·
              refine ⟨8997308137790934994024337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5998205425193956662682891 8997308137790934994024337)
              ·
                refine ⟨6747981103343201245518253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8997308137790934994024337 6747981103343201245518253)
                ·
                  refine ⟨2530492913753700467069345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6747981103343201245518253 2530492913753700467069345)
                  ·
                    refine ⟨1897869685315275350302009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2530492913753700467069345 1897869685315275350302009)
                    ·
                      refine ⟨1423402263986456512726507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1897869685315275350302009 1423402263986456512726507)
                      ·
                        rfl

theorem cell23_2772066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_2772066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772066 prefixEnd_2772066 := by exact prefixLift 2772066
  have htrace : WordTrace (prefixWord ++ tailWord_2772066) baseStart_2772066 baseEnd_2772066 := by
    simpa [prefixWord, tailWord_2772066, baseEnd_2772066] using wordTrace_append hprefix tailTrace_2772066
  have hstable : (prefixWord ++ tailWord_2772066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772066).length < 2 ^ (prefixWord ++ tailWord_2772066).sum := by decide
  have hdescent : baseEnd_2772066 < baseStart_2772066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772068 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 4, 7]
def baseStart_2772068 : Nat := 118140960795 + 2772068 * 2 ^ 59
def prefixEnd_2772068 : Nat := 4983230072969 + 3 ^ 40 * 2772068 * 2
def baseEnd_2772068 : Nat := 474467763649255168300499

theorem tailTrace_2772068 : CollatzResearch.WordTrace tailWord_2772068 prefixEnd_2772068 474467763649255168300499 := by
  unfold tailWord_2772068
  simp only [CollatzResearch.WordTrace]
  refine ⟨50552813060639271183850429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67403750747519028245133905 50552813060639271183850429)
  ·
    refine ⟨18957304897739726693943911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50552813060639271183850429 18957304897739726693943911)
    ·
      refine ⟨28435957346609590040915867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18957304897739726693943911 28435957346609590040915867)
      ·
        refine ⟨42653936019914385061373801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28435957346609590040915867 42653936019914385061373801)
        ·
          refine ⟨31990452014935788796030351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42653936019914385061373801 31990452014935788796030351)
          ·
            refine ⟨47985678022403683194045527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31990452014935788796030351 47985678022403683194045527)
            ·
              refine ⟨71978517033605524791068291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47985678022403683194045527 71978517033605524791068291)
              ·
                refine ⟨107967775550408287186602437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71978517033605524791068291 107967775550408287186602437)
                ·
                  refine ⟨20243957915701553847487957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107967775550408287186602437 20243957915701553847487957)
                  ·
                    refine ⟨474467763649255168300499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20243957915701553847487957 474467763649255168300499)
                    ·
                      rfl

theorem cell23_2772068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_2772068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772068 prefixEnd_2772068 := by exact prefixLift 2772068
  have htrace : WordTrace (prefixWord ++ tailWord_2772068) baseStart_2772068 baseEnd_2772068 := by
    simpa [prefixWord, tailWord_2772068, baseEnd_2772068] using wordTrace_append hprefix tailTrace_2772068
  have hstable : (prefixWord ++ tailWord_2772068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772068).length < 2 ^ (prefixWord ++ tailWord_2772068).sum := by decide
  have hdescent : baseEnd_2772068 < baseStart_2772068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772082 : List Nat := [3, 2, 1, 2, 2, 1, 2, 2, 4, 1, 3]
def baseStart_2772082 : Nat := 118140960795 + 2772082 * 2 ^ 59
def prefixEnd_2772082 : Nat := 4983230072969 + 3 ^ 40 * 2772082 * 2
def baseEnd_2772082 : Nat := 1423410479676928450126433

theorem tailTrace_2772082 : CollatzResearch.WordTrace tailWord_2772082 prefixEnd_2772082 1423410479676928450126433 := by
  unfold tailWord_2772082
  simp only [CollatzResearch.WordTrace]
  refine ⟨25276534185806955689677625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67404091162151881839140333 25276534185806955689677625)
  ·
    refine ⟨18957400639355216767258219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25276534185806955689677625 18957400639355216767258219)
    ·
      refine ⟨28436100959032825150887329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18957400639355216767258219 28436100959032825150887329)
      ·
        refine ⟨21327075719274618863165497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28436100959032825150887329 21327075719274618863165497)
        ·
          refine ⟨15995306789455964147374123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21327075719274618863165497 15995306789455964147374123)
          ·
            refine ⟨23992960184183946221061185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15995306789455964147374123 23992960184183946221061185)
            ·
              refine ⟨17994720138137959665795889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23992960184183946221061185 17994720138137959665795889)
              ·
                refine ⟨13496040103603469749346917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17994720138137959665795889 13496040103603469749346917)
                ·
                  refine ⟨2530507519425650578002547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13496040103603469749346917 2530507519425650578002547)
                  ·
                    refine ⟨3795761279138475867003821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2530507519425650578002547 3795761279138475867003821)
                    ·
                      refine ⟨1423410479676928450126433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3795761279138475867003821 1423410479676928450126433)
                      ·
                        rfl

theorem cell23_2772082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_2772082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772082 prefixEnd_2772082 := by exact prefixLift 2772082
  have htrace : WordTrace (prefixWord ++ tailWord_2772082) baseStart_2772082 baseEnd_2772082 := by
    simpa [prefixWord, tailWord_2772082, baseEnd_2772082] using wordTrace_append hprefix tailTrace_2772082
  have hstable : (prefixWord ++ tailWord_2772082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772082).length < 2 ^ (prefixWord ++ tailWord_2772082).sum := by decide
  have hdescent : baseEnd_2772082 < baseStart_2772082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772125 : List Nat := [1, 4, 2, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_2772125 : Nat := 118140960795 + 2772125 * 2 ^ 59
def prefixEnd_2772125 : Nat := 4983230072969 + 3 ^ 40 * 2772125 * 2
def baseEnd_2772125 : Nat := 1423432559345071781888735

theorem tailTrace_2772125 : CollatzResearch.WordTrace tailWord_2772125 prefixEnd_2772125 1423432559345071781888735 := by
  unfold tailWord_2772125
  simp only [CollatzResearch.WordTrace]
  refine ⟨101107705082072041102525829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67405136721381360735017219 101107705082072041102525829)
  ·
    refine ⟨18957694702888507706723593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101107705082072041102525829 18957694702888507706723593)
    ·
      refine ⟨14218271027166380780042695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18957694702888507706723593 14218271027166380780042695)
      ·
        refine ⟨21327406540749571170064043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14218271027166380780042695 21327406540749571170064043)
        ·
          refine ⟨31991109811124356755096065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21327406540749571170064043 31991109811124356755096065)
          ·
            refine ⟨23993332358343267566322049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31991109811124356755096065 23993332358343267566322049)
            ·
              refine ⟨17994999268757450674741537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23993332358343267566322049 17994999268757450674741537)
              ·
                refine ⟨13496249451568088006056153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17994999268757450674741537 13496249451568088006056153)
                ·
                  refine ⟨10122187088676066004542115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13496249451568088006056153 10122187088676066004542115)
                  ·
                    refine ⟨15183280633014099006813173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10122187088676066004542115 15183280633014099006813173)
                    ·
                      refine ⟨1423432559345071781888735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15183280633014099006813173 1423432559345071781888735)
                      ·
                        rfl

theorem cell23_2772125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_2772125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772125 prefixEnd_2772125 := by exact prefixLift 2772125
  have htrace : WordTrace (prefixWord ++ tailWord_2772125) baseStart_2772125 baseEnd_2772125 := by
    simpa [prefixWord, tailWord_2772125, baseEnd_2772125] using wordTrace_append hprefix tailTrace_2772125
  have hstable : (prefixWord ++ tailWord_2772125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772125).length < 2 ^ (prefixWord ++ tailWord_2772125).sum := by decide
  have hdescent : baseEnd_2772125 < baseStart_2772125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772126 : List Nat := [4, 3, 1, 1, 2, 1, 1, 4, 1, 3, 2]
def baseStart_2772126 : Nat := 118140960795 + 2772126 * 2 ^ 59
def prefixEnd_2772126 : Nat := 4983230072969 + 3 ^ 40 * 2772126 * 2
def baseEnd_2772126 : Nat := 1423433072825726277976231

theorem tailTrace_2772126 : CollatzResearch.WordTrace tailWord_2772126 prefixEnd_2772126 1423433072825726277976231 := by
  unfold tailWord_2772126
  simp only [CollatzResearch.WordTrace]
  refine ⟨12638467694383552284164029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67405161036712278848874821 12638467694383552284164029)
  ·
    refine ⟨4739425385393832106561511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12638467694383552284164029 4739425385393832106561511)
    ·
      refine ⟨7109138078090748159842267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4739425385393832106561511 7109138078090748159842267)
      ·
        refine ⟨10663707117136122239763401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7109138078090748159842267 10663707117136122239763401)
        ·
          refine ⟨7997780337852091679822551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10663707117136122239763401 7997780337852091679822551)
          ·
            refine ⟨11996670506778137519733827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7997780337852091679822551 11996670506778137519733827)
            ·
              refine ⟨17995005760167206279600741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11996670506778137519733827 17995005760167206279600741)
              ·
                refine ⟨3374063580031351177425139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17995005760167206279600741 3374063580031351177425139)
                ·
                  refine ⟨5061095370047026766137709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3374063580031351177425139 5061095370047026766137709)
                  ·
                    refine ⟨1897910763767635037301641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5061095370047026766137709 1897910763767635037301641)
                    ·
                      refine ⟨1423433072825726277976231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1897910763767635037301641 1423433072825726277976231)
                      ·
                        rfl

theorem cell23_2772126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_2772126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772126 prefixEnd_2772126 := by exact prefixLift 2772126
  have htrace : WordTrace (prefixWord ++ tailWord_2772126) baseStart_2772126 baseEnd_2772126 := by
    simpa [prefixWord, tailWord_2772126, baseEnd_2772126] using wordTrace_append hprefix tailTrace_2772126
  have hstable : (prefixWord ++ tailWord_2772126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772126).length < 2 ^ (prefixWord ++ tailWord_2772126).sum := by decide
  have hdescent : baseEnd_2772126 < baseStart_2772126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772155 : List Nat := [1, 1, 1, 1, 1, 2, 4, 4, 2, 3, 3]
def baseStart_2772155 : Nat := 118140960795 + 2772155 * 2 ^ 59
def prefixEnd_2772155 : Nat := 4983230072969 + 3 ^ 40 * 2772155 * 2
def baseEnd_2772155 : Nat := 1423447963764706664513597

theorem tailTrace_2772155 : CollatzResearch.WordTrace tailWord_2772155 prefixEnd_2772155 1423447963764706664513597 := by
  unfold tailWord_2772155
  simp only [CollatzResearch.WordTrace]
  refine ⟨101108799271963356226117919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67405866181308904150745279 101108799271963356226117919)
  ·
    refine ⟨151663198907945034339176879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101108799271963356226117919 151663198907945034339176879)
    ·
      refine ⟨227494798361917551508765319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151663198907945034339176879 227494798361917551508765319)
      ·
        refine ⟨341242197542876327263147979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227494798361917551508765319 341242197542876327263147979)
        ·
          refine ⟨511863296314314490894721969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341242197542876327263147979 511863296314314490894721969)
          ·
            refine ⟨383897472235735868171041477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 511863296314314490894721969 383897472235735868171041477)
            ·
              refine ⟨71980776044200475282070277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 383897472235735868171041477 71980776044200475282070277)
              ·
                refine ⟨13496395508287589115388177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71980776044200475282070277 13496395508287589115388177)
                ·
                  refine ⟨10122296631215691836541133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13496395508287589115388177 10122296631215691836541133)
                  ·
                    refine ⟨3795861236705884438702925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10122296631215691836541133 3795861236705884438702925)
                    ·
                      refine ⟨1423447963764706664513597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3795861236705884438702925 1423447963764706664513597)
                      ·
                        rfl

theorem cell23_2772155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3, 3].length) (baseStart_2772155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772155 prefixEnd_2772155 := by exact prefixLift 2772155
  have htrace : WordTrace (prefixWord ++ tailWord_2772155) baseStart_2772155 baseEnd_2772155 := by
    simpa [prefixWord, tailWord_2772155, baseEnd_2772155] using wordTrace_append hprefix tailTrace_2772155
  have hstable : (prefixWord ++ tailWord_2772155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772155).length < 2 ^ (prefixWord ++ tailWord_2772155).sum := by decide
  have hdescent : baseEnd_2772155 < baseStart_2772155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772192 : List Nat := [2, 1, 1, 3, 1, 5, 2, 1, 2, 5]
def baseStart_2772192 : Nat := 118140960795 + 2772192 * 2 ^ 59
def prefixEnd_2772192 : Nat := 4983230072969 + 3 ^ 40 * 2772192 * 2
def baseEnd_2772192 : Nat := 474488987516307673250309

theorem tailTrace_2772192 : CollatzResearch.WordTrace tailWord_2772192 prefixEnd_2772192 474488987516307673250309 := by
  unfold tailWord_2772192
  simp only [CollatzResearch.WordTrace]
  refine ⟨50555074386414655772607415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67406765848552874363476553 50555074386414655772607415)
  ·
    refine ⟨75832611579621983658911123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50555074386414655772607415 75832611579621983658911123)
    ·
      refine ⟨113748917369432975488366685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75832611579621983658911123 113748917369432975488366685)
      ·
        refine ⟨42655844013537365808137507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113748917369432975488366685 42655844013537365808137507)
        ·
          refine ⟨63983766020306048712206261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42655844013537365808137507 63983766020306048712206261)
          ·
            refine ⟨5998478064403692066769337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63983766020306048712206261 5998478064403692066769337)
            ·
              refine ⟨4498858548302769050077003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5998478064403692066769337 4498858548302769050077003)
              ·
                refine ⟨6748287822454153575115505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4498858548302769050077003 6748287822454153575115505)
                ·
                  refine ⟨5061215866840615181336629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6748287822454153575115505 5061215866840615181336629)
                  ·
                    refine ⟨474488987516307673250309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5061215866840615181336629 474488987516307673250309)
                    ·
                      rfl

theorem cell23_2772192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 2, 5].length) (baseStart_2772192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772192 prefixEnd_2772192 := by exact prefixLift 2772192
  have htrace : WordTrace (prefixWord ++ tailWord_2772192) baseStart_2772192 baseEnd_2772192 := by
    simpa [prefixWord, tailWord_2772192, baseEnd_2772192] using wordTrace_append hprefix tailTrace_2772192
  have hstable : (prefixWord ++ tailWord_2772192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772192).length < 2 ^ (prefixWord ++ tailWord_2772192).sum := by decide
  have hdescent : baseEnd_2772192 < baseStart_2772192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772269 : List Nat := [1, 5, 3, 1, 1, 2, 1, 1, 8]
def baseStart_2772269 : Nat := 118140960795 + 2772269 * 2 ^ 59
def prefixEnd_2772269 : Nat := 4983230072969 + 3 ^ 40 * 2772269 * 2
def baseEnd_2772269 : Nat := 158167388951035468720897

theorem tailTrace_2772269 : CollatzResearch.WordTrace tailWord_2772269 prefixEnd_2772269 158167388951035468720897 := by
  unfold tailWord_2772269
  simp only [CollatzResearch.WordTrace]
  refine ⟨101112957193550353695767861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67408638129033569130511907 101112957193550353695767861)
  ·
    refine ⟨9479339736895345658978237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101112957193550353695767861 9479339736895345658978237)
    ·
      refine ⟨3554752401335754622116839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9479339736895345658978237 3554752401335754622116839)
      ·
        refine ⟨5332128602003631933175259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3554752401335754622116839 5332128602003631933175259)
        ·
          refine ⟨7998192903005447899762889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5332128602003631933175259 7998192903005447899762889)
          ·
            refine ⟨5998644677254085924822167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7998192903005447899762889 5998644677254085924822167)
            ·
              refine ⟨8997967015881128887233251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5998644677254085924822167 8997967015881128887233251)
              ·
                refine ⟨13496950523821693330849877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8997967015881128887233251 13496950523821693330849877)
                ·
                  refine ⟨158167388951035468720897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13496950523821693330849877 158167388951035468720897)
                  ·
                    rfl

theorem cell23_2772269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_2772269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772269 prefixEnd_2772269 := by exact prefixLift 2772269
  have htrace : WordTrace (prefixWord ++ tailWord_2772269) baseStart_2772269 baseEnd_2772269 := by
    simpa [prefixWord, tailWord_2772269, baseEnd_2772269] using wordTrace_append hprefix tailTrace_2772269
  have hstable : (prefixWord ++ tailWord_2772269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772269).length < 2 ^ (prefixWord ++ tailWord_2772269).sum := by decide
  have hdescent : baseEnd_2772269 < baseStart_2772269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772312 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 6, 4]
def baseStart_2772312 : Nat := 118140960795 + 2772312 * 2 ^ 59
def prefixEnd_2772312 : Nat := 4983230072969 + 3 ^ 40 * 2772312 * 2
def baseEnd_2772312 : Nat := 474509526742487516750125

theorem tailTrace_2772312 : CollatzResearch.WordTrace tailWord_2772312 prefixEnd_2772312 474509526742487516750125 := by
  unfold tailWord_2772312
  simp only [CollatzResearch.WordTrace]
  refine ⟨50557262766197286019791595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67409683688263048026388793 50557262766197286019791595)
  ·
    refine ⟨75835894149295929029687393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50557262766197286019791595 75835894149295929029687393)
    ·
      refine ⟨56876920611971946772265545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75835894149295929029687393 56876920611971946772265545)
      ·
        refine ⟨42657690458978960079199159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56876920611971946772265545 42657690458978960079199159)
        ·
          refine ⟨63986535688468440118798739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42657690458978960079199159 63986535688468440118798739)
          ·
            refine ⟨95979803532702660178198109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63986535688468440118798739 95979803532702660178198109)
            ·
              refine ⟨35992426324763497566824291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95979803532702660178198109 35992426324763497566824291)
              ·
                refine ⟨53988639487145246350236437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35992426324763497566824291 53988639487145246350236437)
                ·
                  refine ⟨2530717475959933422667333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53988639487145246350236437 2530717475959933422667333)
                  ·
                    refine ⟨474509526742487516750125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2530717475959933422667333 474509526742487516750125)
                    ·
                      rfl

theorem cell23_2772312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 6, 4].length) (baseStart_2772312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772312 prefixEnd_2772312 := by exact prefixLift 2772312
  have htrace : WordTrace (prefixWord ++ tailWord_2772312) baseStart_2772312 baseEnd_2772312 := by
    simpa [prefixWord, tailWord_2772312, baseEnd_2772312] using wordTrace_append hprefix tailTrace_2772312
  have hstable : (prefixWord ++ tailWord_2772312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772312).length < 2 ^ (prefixWord ++ tailWord_2772312).sum := by decide
  have hdescent : baseEnd_2772312 < baseStart_2772312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772330 : List Nat := [3, 1, 3, 3, 3, 1, 1, 1, 3, 1, 3]
def baseStart_2772330 : Nat := 118140960795 + 2772330 * 2 ^ 59
def prefixEnd_2772330 : Nat := 4983230072969 + 3 ^ 40 * 2772330 * 2
def baseEnd_2772330 : Nat := 1423537822879243479825293

theorem tailTrace_2772330 : CollatzResearch.WordTrace tailWord_2772330 prefixEnd_2772330 1423537822879243479825293 := by
  unfold tailWord_2772330
  simp only [CollatzResearch.WordTrace]
  refine ⟨25278795511582340278434611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67410121364219574075825629 25278795511582340278434611)
  ·
    refine ⟨37918193267373510417651917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25278795511582340278434611 37918193267373510417651917)
    ·
      refine ⟨14219322475265066406619469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37918193267373510417651917 14219322475265066406619469)
      ·
        refine ⟨5332245928224399902482301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14219322475265066406619469 5332245928224399902482301)
        ·
          refine ⟨1999592223084149963430863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5332245928224399902482301 1999592223084149963430863)
          ·
            refine ⟨2999388334626224945146295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1999592223084149963430863 2999388334626224945146295)
            ·
              refine ⟨4499082501939337417719443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2999388334626224945146295 4499082501939337417719443)
              ·
                refine ⟨6748623752909006126579165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4499082501939337417719443 6748623752909006126579165)
                ·
                  refine ⟨2530733907340877297467187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6748623752909006126579165 2530733907340877297467187)
                  ·
                    refine ⟨3796100861011315946200781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2530733907340877297467187 3796100861011315946200781)
                    ·
                      refine ⟨1423537822879243479825293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3796100861011315946200781 1423537822879243479825293)
                      ·
                        rfl

theorem cell23_2772330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_2772330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772330 prefixEnd_2772330 := by exact prefixLift 2772330
  have htrace : WordTrace (prefixWord ++ tailWord_2772330) baseStart_2772330 baseEnd_2772330 := by
    simpa [prefixWord, tailWord_2772330, baseEnd_2772330] using wordTrace_append hprefix tailTrace_2772330
  have hstable : (prefixWord ++ tailWord_2772330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772330).length < 2 ^ (prefixWord ++ tailWord_2772330).sum := by decide
  have hdescent : baseEnd_2772330 < baseStart_2772330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772332 : List Nat := [2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 6]
def baseStart_2772332 : Nat := 118140960795 + 2772332 * 2 ^ 59
def prefixEnd_2772332 : Nat := 4983230072969 + 3 ^ 40 * 2772332 * 2
def baseEnd_2772332 : Nat := 1423538849840552472000283

theorem tailTrace_2772332 : CollatzResearch.WordTrace tailWord_2772332 prefixEnd_2772332 1423538849840552472000283 := by
  unfold tailWord_2772332
  simp only [CollatzResearch.WordTrace]
  refine ⟨50557627496161057727655625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67410169994881410303540833 50557627496161057727655625)
  ·
    refine ⟨37918220622120793295741719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50557627496161057727655625 37918220622120793295741719)
    ·
      refine ⟨56877330933181189943612579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37918220622120793295741719 56877330933181189943612579)
      ·
        refine ⟨85315996399771784915418869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56877330933181189943612579 85315996399771784915418869)
        ·
          refine ⟨7998374662478604835820519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85315996399771784915418869 7998374662478604835820519)
          ·
            refine ⟨11997561993717907253730779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7998374662478604835820519 11997561993717907253730779)
            ·
              refine ⟨17996342990576860880596169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11997561993717907253730779 17996342990576860880596169)
              ·
                refine ⟨13497257242932645660447127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17996342990576860880596169 13497257242932645660447127)
                ·
                  refine ⟨20245885864398968490670691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13497257242932645660447127 20245885864398968490670691)
                  ·
                    refine ⟨30368828796598452736006037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20245885864398968490670691 30368828796598452736006037)
                    ·
                      refine ⟨1423538849840552472000283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30368828796598452736006037 1423538849840552472000283)
                      ·
                        rfl

theorem cell23_2772332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_2772332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772332 prefixEnd_2772332 := by exact prefixLift 2772332
  have htrace : WordTrace (prefixWord ++ tailWord_2772332) baseStart_2772332 baseEnd_2772332 := by
    simpa [prefixWord, tailWord_2772332, baseEnd_2772332] using wordTrace_append hprefix tailTrace_2772332
  have hstable : (prefixWord ++ tailWord_2772332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772332).length < 2 ^ (prefixWord ++ tailWord_2772332).sum := by decide
  have hdescent : baseEnd_2772332 < baseStart_2772332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772350 : List Nat := [4, 2, 3, 2, 1, 2, 1, 2, 1, 5]
def baseStart_2772350 : Nat := 118140960795 + 2772350 * 2 ^ 59
def prefixEnd_2772350 : Nat := 4983230072969 + 3 ^ 40 * 2772350 * 2
def baseEnd_2772350 : Nat := 474516030830777800525067

theorem tailTrace_2772350 : CollatzResearch.WordTrace tailWord_2772350 prefixEnd_2772350 474516030830777800525067 := by
  unfold tailWord_2772350
  simp only [CollatzResearch.WordTrace]
  refine ⟨12639488938282113066183313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67410607670837936352977669 12639488938282113066183313)
  ·
    refine ⟨9479616703711584799637485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12639488938282113066183313 9479616703711584799637485)
    ·
      refine ⟨3554856263891844299864057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9479616703711584799637485 3554856263891844299864057)
      ·
        refine ⟨2666142197918883224898043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3554856263891844299864057 2666142197918883224898043)
        ·
          refine ⟨3999213296878324837347065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2666142197918883224898043 3999213296878324837347065)
          ·
            refine ⟨2999409972658743628010299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3999213296878324837347065 2999409972658743628010299)
            ·
              refine ⟨4499114958988115442015449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2999409972658743628010299 4499114958988115442015449)
              ·
                refine ⟨3374336219241086581511587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4499114958988115442015449 3374336219241086581511587)
                ·
                  refine ⟨5061504328861629872267381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3374336219241086581511587 5061504328861629872267381)
                  ·
                    refine ⟨474516030830777800525067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5061504328861629872267381 474516030830777800525067)
                    ·
                      rfl

theorem cell23_2772350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_2772350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772350 prefixEnd_2772350 := by exact prefixLift 2772350
  have htrace : WordTrace (prefixWord ++ tailWord_2772350) baseStart_2772350 baseEnd_2772350 := by
    simpa [prefixWord, tailWord_2772350, baseEnd_2772350] using wordTrace_append hprefix tailTrace_2772350
  have hstable : (prefixWord ++ tailWord_2772350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772350).length < 2 ^ (prefixWord ++ tailWord_2772350).sum := by decide
  have hdescent : baseEnd_2772350 < baseStart_2772350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772352 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 3]
def baseStart_2772352 : Nat := 118140960795 + 2772352 * 2 ^ 59
def prefixEnd_2772352 : Nat := 4983230072969 + 3 ^ 40 * 2772352 * 2
def baseEnd_2772352 : Nat := 1423549119453642393750191

theorem tailTrace_2772352 : CollatzResearch.WordTrace tailWord_2772352 prefixEnd_2772352 1423549119453642393750191 := by
  unfold tailWord_2772352
  simp only [CollatzResearch.WordTrace]
  refine ⟨50557992226124829435519655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67410656301499772580692873 50557992226124829435519655)
  ·
    refine ⟨75836988339187244153279483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50557992226124829435519655 75836988339187244153279483)
    ·
      refine ⟨113755482508780866229919225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75836988339187244153279483 113755482508780866229919225)
      ·
        refine ⟨85316611881585649672439419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113755482508780866229919225 85316611881585649672439419)
        ·
          refine ⟨127974917822378474508659129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85316611881585649672439419 127974917822378474508659129)
          ·
            refine ⟨95981188366783855881494347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127974917822378474508659129 95981188366783855881494347)
            ·
              refine ⟨143971782550175783822241521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95981188366783855881494347 143971782550175783822241521)
              ·
                refine ⟨107978836912631837866681141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143971782550175783822241521 107978836912631837866681141)
                ·
                  refine ⟨10123015960559234800001357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107978836912631837866681141 10123015960559234800001357)
                  ·
                    refine ⟨3796130985209713050000509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10123015960559234800001357 3796130985209713050000509)
                    ·
                      refine ⟨1423549119453642393750191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3796130985209713050000509 1423549119453642393750191)
                      ·
                        rfl

theorem cell23_2772352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 3].length) (baseStart_2772352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772352 prefixEnd_2772352 := by exact prefixLift 2772352
  have htrace : WordTrace (prefixWord ++ tailWord_2772352) baseStart_2772352 baseEnd_2772352 := by
    simpa [prefixWord, tailWord_2772352, baseEnd_2772352] using wordTrace_append hprefix tailTrace_2772352
  have hstable : (prefixWord ++ tailWord_2772352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772352).length < 2 ^ (prefixWord ++ tailWord_2772352).sum := by decide
  have hdescent : baseEnd_2772352 < baseStart_2772352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772353 : List Nat := [1, 2, 4, 3, 2, 2, 1, 2, 1, 1, 4]
def baseStart_2772353 : Nat := 118140960795 + 2772353 * 2 ^ 59
def prefixEnd_2772353 : Nat := 4983230072969 + 3 ^ 40 * 2772353 * 2
def baseEnd_2772353 : Nat := 1423549632934296889837687

theorem tailTrace_2772353 : CollatzResearch.WordTrace tailWord_2772353 prefixEnd_2772353 1423549632934296889837687 := by
  unfold tailWord_2772353
  simp only [CollatzResearch.WordTrace]
  refine ⟨101116020925246036041825713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67410680616830690694550475 101116020925246036041825713)
  ·
    refine ⟨75837015693934527031369285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101116020925246036041825713 75837015693934527031369285)
    ·
      refine ⟨14219440442612723818381741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75837015693934527031369285 14219440442612723818381741)
      ·
        refine ⟨5332290165979771431893153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14219440442612723818381741 5332290165979771431893153)
        ·
          refine ⟨3999217624484828573919865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5332290165979771431893153 3999217624484828573919865)
          ·
            refine ⟨2999413218363621430439899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3999217624484828573919865 2999413218363621430439899)
            ·
              refine ⟨4499119827545432145659849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2999413218363621430439899 4499119827545432145659849)
              ·
                refine ⟨3374339870659074109244887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4499119827545432145659849 3374339870659074109244887)
                ·
                  refine ⟨5061509805988611163867331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3374339870659074109244887 5061509805988611163867331)
                  ·
                    refine ⟨7592264708982916745800997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5061509805988611163867331 7592264708982916745800997)
                    ·
                      refine ⟨1423549632934296889837687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7592264708982916745800997 1423549632934296889837687)
                      ·
                        rfl

theorem cell23_2772353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_2772353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772353 prefixEnd_2772353 := by exact prefixLift 2772353
  have htrace : WordTrace (prefixWord ++ tailWord_2772353) baseStart_2772353 baseEnd_2772353 := by
    simpa [prefixWord, tailWord_2772353, baseEnd_2772353] using wordTrace_append hprefix tailTrace_2772353
  have hstable : (prefixWord ++ tailWord_2772353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772353).length < 2 ^ (prefixWord ++ tailWord_2772353).sum := by decide
  have hdescent : baseEnd_2772353 < baseStart_2772353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772356 : List Nat := [2, 3, 2, 1, 1, 3, 3, 2, 1, 2, 3]
def baseStart_2772356 : Nat := 118140960795 + 2772356 * 2 ^ 59
def prefixEnd_2772356 : Nat := 4983230072969 + 3 ^ 40 * 2772356 * 2
def baseEnd_2772356 : Nat := 1423551173376260378100173

theorem tailTrace_2772356 : CollatzResearch.WordTrace tailWord_2772356 prefixEnd_2772356 1423551173376260378100173 := by
  unfold tailWord_2772356
  simp only [CollatzResearch.WordTrace]
  refine ⟨50558065172117583777092461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67410753562823445036123281 50558065172117583777092461)
  ·
    refine ⟨18959274439544093916409673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50558065172117583777092461 18959274439544093916409673)
    ·
      refine ⟨14219455829658070437307255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18959274439544093916409673 14219455829658070437307255)
      ·
        refine ⟨21329183744487105655960883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14219455829658070437307255 21329183744487105655960883)
        ·
          refine ⟨31993775616730658483941325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21329183744487105655960883 31993775616730658483941325)
          ·
            refine ⟨11997665856273996931477997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31993775616730658483941325 11997665856273996931477997)
            ·
              refine ⟨4499124696102748849304249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11997665856273996931477997 4499124696102748849304249)
              ·
                refine ⟨3374343522077061636978187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4499124696102748849304249 3374343522077061636978187)
                ·
                  refine ⟨5061515283115592455467281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3374343522077061636978187 5061515283115592455467281)
                  ·
                    refine ⟨3796136462336694341600461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5061515283115592455467281 3796136462336694341600461)
                    ·
                      refine ⟨1423551173376260378100173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3796136462336694341600461 1423551173376260378100173)
                      ·
                        rfl

theorem cell23_2772356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_2772356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772356 prefixEnd_2772356 := by exact prefixLift 2772356
  have htrace : WordTrace (prefixWord ++ tailWord_2772356) baseStart_2772356 baseEnd_2772356 := by
    simpa [prefixWord, tailWord_2772356, baseEnd_2772356] using wordTrace_append hprefix tailTrace_2772356
  have hstable : (prefixWord ++ tailWord_2772356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772356).length < 2 ^ (prefixWord ++ tailWord_2772356).sum := by decide
  have hdescent : baseEnd_2772356 < baseStart_2772356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772366 : List Nat := [4, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4]
def baseStart_2772366 : Nat := 118140960795 + 2772366 * 2 ^ 59
def prefixEnd_2772366 : Nat := 4983230072969 + 3 ^ 40 * 2772366 * 2
def baseEnd_2772366 : Nat := 1423556308182805338975127

theorem tailTrace_2772366 : CollatzResearch.WordTrace tailWord_2772366 prefixEnd_2772366 1423556308182805338975127 := by
  unfold tailWord_2772366
  simp only [CollatzResearch.WordTrace]
  refine ⟨12639561884274867407756119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67410996716132626174699301 12639561884274867407756119)
  ·
    refine ⟨18959342826412301111634179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12639561884274867407756119 18959342826412301111634179)
    ·
      refine ⟨28439014239618451667451269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18959342826412301111634179 28439014239618451667451269)
      ·
        refine ⟨5332315169928459687647113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28439014239618451667451269 5332315169928459687647113)
        ·
          refine ⟨3999236377446344765735335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5332315169928459687647113 3999236377446344765735335)
          ·
            refine ⟨5998854566169517148603003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3999236377446344765735335 5998854566169517148603003)
            ·
              refine ⟨8998281849254275722904505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5998854566169517148603003 8998281849254275722904505)
              ·
                refine ⟨6748711386940706792178379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8998281849254275722904505 6748711386940706792178379)
                ·
                  refine ⟨10123067080411060188267569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6748711386940706792178379 10123067080411060188267569)
                  ·
                    refine ⟨7592300310308295141200677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10123067080411060188267569 7592300310308295141200677)
                    ·
                      refine ⟨1423556308182805338975127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7592300310308295141200677 1423556308182805338975127)
                      ·
                        rfl

theorem cell23_2772366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_2772366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772366 prefixEnd_2772366 := by exact prefixLift 2772366
  have htrace : WordTrace (prefixWord ++ tailWord_2772366) baseStart_2772366 baseEnd_2772366 := by
    simpa [prefixWord, tailWord_2772366, baseEnd_2772366] using wordTrace_append hprefix tailTrace_2772366
  have hstable : (prefixWord ++ tailWord_2772366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772366).length < 2 ^ (prefixWord ++ tailWord_2772366).sum := by decide
  have hdescent : baseEnd_2772366 < baseStart_2772366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772370 : List Nat := [3, 2, 3, 3, 1, 1, 3, 1, 1, 1, 4]
def baseStart_2772370 : Nat := 118140960795 + 2772370 * 2 ^ 59
def prefixEnd_2772370 : Nat := 4983230072969 + 3 ^ 40 * 2772370 * 2
def baseEnd_2772370 : Nat := 1423558362105423323325109

theorem tailTrace_2772370 : CollatzResearch.WordTrace tailWord_2772370 prefixEnd_2772370 1423558362105423323325109 := by
  unfold tailWord_2772370
  simp only [CollatzResearch.WordTrace]
  refine ⟨25279160241546111986298641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67411093977456298630129709 25279160241546111986298641)
  ·
    refine ⟨18959370181159583989723981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25279160241546111986298641 18959370181159583989723981)
    ·
      refine ⟨7109763817934843996146493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18959370181159583989723981 7109763817934843996146493)
      ·
        refine ⟨2666161431725566498554935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7109763817934843996146493 2666161431725566498554935)
        ·
          refine ⟨3999242147588349747832403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2666161431725566498554935 3999242147588349747832403)
          ·
            refine ⟨5998863221382524621748605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3999242147588349747832403 5998863221382524621748605)
            ·
              refine ⟨2249573708018446733155727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5998863221382524621748605 2249573708018446733155727)
              ·
                refine ⟨3374360562027670099733591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2249573708018446733155727 3374360562027670099733591)
                ·
                  refine ⟨5061540843041505149600387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3374360562027670099733591 5061540843041505149600387)
                  ·
                    refine ⟨7592311264562257724400581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5061540843041505149600387 7592311264562257724400581)
                    ·
                      refine ⟨1423558362105423323325109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7592311264562257724400581 1423558362105423323325109)
                      ·
                        rfl

theorem cell23_2772370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_2772370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772370 prefixEnd_2772370 := by exact prefixLift 2772370
  have htrace : WordTrace (prefixWord ++ tailWord_2772370) baseStart_2772370 baseEnd_2772370 := by
    simpa [prefixWord, tailWord_2772370, baseEnd_2772370] using wordTrace_append hprefix tailTrace_2772370
  have hstable : (prefixWord ++ tailWord_2772370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772370).length < 2 ^ (prefixWord ++ tailWord_2772370).sum := by decide
  have hdescent : baseEnd_2772370 < baseStart_2772370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772426 : List Nat := [3, 1, 2, 1, 2, 3, 2, 2, 1, 4, 2]
def baseStart_2772426 : Nat := 118140960795 + 2772426 * 2 ^ 59
def prefixEnd_2772426 : Nat := 4983230072969 + 3 ^ 40 * 2772426 * 2
def baseEnd_2772426 : Nat := 1423587117022075104224851

theorem tailTrace_2772426 : CollatzResearch.WordTrace tailWord_2772426 prefixEnd_2772426 1423587117022075104224851 := by
  unfold tailWord_2772426
  simp only [CollatzResearch.WordTrace]
  refine ⟨25279670863495392377308283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67412455635987713006155421 25279670863495392377308283)
  ·
    refine ⟨37919506295243088565962425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25279670863495392377308283 37919506295243088565962425)
    ·
      refine ⟨28439629721432316424471819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37919506295243088565962425 28439629721432316424471819)
      ·
        refine ⟨42659444582148474636707729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28439629721432316424471819 42659444582148474636707729)
        ·
          refine ⟨31994583436611355977530797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42659444582148474636707729 31994583436611355977530797)
          ·
            refine ⟨11997968788729258491574049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31994583436611355977530797 11997968788729258491574049)
            ·
              refine ⟨8998476591546943868680537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11997968788729258491574049 8998476591546943868680537)
              ·
                refine ⟨6748857443660207901510403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8998476591546943868680537 6748857443660207901510403)
                ·
                  refine ⟨10123286165490311852265605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6748857443660207901510403 10123286165490311852265605)
                  ·
                    refine ⟨1898116156029433472299801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10123286165490311852265605 1898116156029433472299801)
                    ·
                      refine ⟨1423587117022075104224851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1898116156029433472299801 1423587117022075104224851)
                      ·
                        rfl

theorem cell23_2772426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 1, 4, 2].length) (baseStart_2772426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772426 prefixEnd_2772426 := by exact prefixLift 2772426
  have htrace : WordTrace (prefixWord ++ tailWord_2772426) baseStart_2772426 baseEnd_2772426 := by
    simpa [prefixWord, tailWord_2772426, baseEnd_2772426] using wordTrace_append hprefix tailTrace_2772426
  have hstable : (prefixWord ++ tailWord_2772426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772426).length < 2 ^ (prefixWord ++ tailWord_2772426).sum := by decide
  have hdescent : baseEnd_2772426 < baseStart_2772426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772449 : List Nat := [1, 2, 3, 1, 2, 4, 2, 1, 7]
def baseStart_2772449 : Nat := 118140960795 + 2772449 * 2 ^ 59
def prefixEnd_2772449 : Nat := 4983230072969 + 3 ^ 40 * 2772449 * 2
def baseEnd_2772449 : Nat := 158177658564125390470805

theorem tailTrace_2772449 : CollatzResearch.WordTrace tailWord_2772449 prefixEnd_2772449 158177658564125390470805 := by
  unfold tailWord_2772449
  simp only [CollatzResearch.WordTrace]
  refine ⟨101119522332898244437320401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67413014888598829624880267 101119522332898244437320401)
  ·
    refine ⟨75839641749673683327990301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101119522332898244437320401 75839641749673683327990301)
    ·
      refine ⟨28439865656127631247996363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75839641749673683327990301 28439865656127631247996363)
      ·
        refine ⟨42659798484191446871994545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28439865656127631247996363 42659798484191446871994545)
        ·
          refine ⟨31994848863143585153995909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42659798484191446871994545 31994848863143585153995909)
          ·
            refine ⟨5999034161839422216374233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31994848863143585153995909 5999034161839422216374233)
            ·
              refine ⟨4499275621379566662280675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5999034161839422216374233 4499275621379566662280675)
              ·
                refine ⟨6748913432069349993421013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4499275621379566662280675 6748913432069349993421013)
                ·
                  refine ⟨158177658564125390470805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6748913432069349993421013 158177658564125390470805)
                  ·
                    rfl

theorem cell23_2772449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 7].length) (baseStart_2772449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772449 prefixEnd_2772449 := by exact prefixLift 2772449
  have htrace : WordTrace (prefixWord ++ tailWord_2772449) baseStart_2772449 baseEnd_2772449 := by
    simpa [prefixWord, tailWord_2772449, baseEnd_2772449] using wordTrace_append hprefix tailTrace_2772449
  have hstable : (prefixWord ++ tailWord_2772449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772449).length < 2 ^ (prefixWord ++ tailWord_2772449).sum := by decide
  have hdescent : baseEnd_2772449 < baseStart_2772449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772499 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 4]
def baseStart_2772499 : Nat := 118140960795 + 2772499 * 2 ^ 59
def prefixEnd_2772499 : Nat := 4983230072969 + 3 ^ 40 * 2772499 * 2
def baseEnd_2772499 : Nat := 1423624601109853318612015

theorem tailTrace_2772499 : CollatzResearch.WordTrace tailWord_2772499 prefixEnd_2772499 1423624601109853318612015 := by
  unfold tailWord_2772499
  simp only [CollatzResearch.WordTrace]
  refine ⟨101121345982717102976640551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67414230655144735317760367 101121345982717102976640551)
  ·
    refine ⟨151682018974075654464960827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101121345982717102976640551 151682018974075654464960827)
    ·
      refine ⟨227523028461113481697441241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151682018974075654464960827 227523028461113481697441241)
      ·
        refine ⟨170642271345835111273080931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227523028461113481697441241 170642271345835111273080931)
        ·
          refine ⟨255963407018752666909621397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170642271345835111273080931 255963407018752666909621397)
          ·
            refine ⟨11998284704004031261388503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 255963407018752666909621397 11998284704004031261388503)
            ·
              refine ⟨17997427056006046892082755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11998284704004031261388503 17997427056006046892082755)
              ·
                refine ⟨26996140584009070338124133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17997427056006046892082755 26996140584009070338124133)
                ·
                  refine ⟨5061776359501700688398275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26996140584009070338124133 5061776359501700688398275)
                  ·
                    refine ⟨7592664539252551032597413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5061776359501700688398275 7592664539252551032597413)
                    ·
                      refine ⟨1423624601109853318612015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7592664539252551032597413 1423624601109853318612015)
                      ·
                        rfl

theorem cell23_2772499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 4].length) (baseStart_2772499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772499 prefixEnd_2772499 := by exact prefixLift 2772499
  have htrace : WordTrace (prefixWord ++ tailWord_2772499) baseStart_2772499 baseEnd_2772499 := by
    simpa [prefixWord, tailWord_2772499, baseEnd_2772499] using wordTrace_append hprefix tailTrace_2772499
  have hstable : (prefixWord ++ tailWord_2772499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772499).length < 2 ^ (prefixWord ++ tailWord_2772499).sum := by decide
  have hdescent : baseEnd_2772499 < baseStart_2772499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772500 : List Nat := [2, 4, 3, 1, 3, 1, 1, 1, 7]
def baseStart_2772500 : Nat := 118140960795 + 2772500 * 2 ^ 59
def prefixEnd_2772500 : Nat := 4983230072969 + 3 ^ 40 * 2772500 * 2
def baseEnd_2772500 : Nat := 158180568287834201633279

theorem tailTrace_2772500 : CollatzResearch.WordTrace tailWord_2772500 prefixEnd_2772500 158180568287834201633279 := by
  unfold tailWord_2772500
  simp only [CollatzResearch.WordTrace]
  refine ⟨50560691227856740073713477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67414254970475653431617969 50560691227856740073713477)
  ·
    refine ⟨9480129605223138763821277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50560691227856740073713477 9480129605223138763821277)
    ·
      refine ⟨3555048601958677036432979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9480129605223138763821277 3555048601958677036432979)
      ·
        refine ⟨5332572902938015554649469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3555048601958677036432979 5332572902938015554649469)
        ·
          refine ⟨1999714838601755832993551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5332572902938015554649469 1999714838601755832993551)
          ·
            refine ⟨2999572257902633749490327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1999714838601755832993551 2999572257902633749490327)
            ·
              refine ⟨4499358386853950624235491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2999572257902633749490327 4499358386853950624235491)
              ·
                refine ⟨6749037580280925936353237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4499358386853950624235491 6749037580280925936353237)
                ·
                  refine ⟨158180568287834201633279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6749037580280925936353237 158180568287834201633279)
                  ·
                    rfl

theorem cell23_2772500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_2772500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772500 prefixEnd_2772500 := by exact prefixLift 2772500
  have htrace : WordTrace (prefixWord ++ tailWord_2772500) baseStart_2772500 baseEnd_2772500 := by
    simpa [prefixWord, tailWord_2772500, baseEnd_2772500] using wordTrace_append hprefix tailTrace_2772500
  have hstable : (prefixWord ++ tailWord_2772500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772500).length < 2 ^ (prefixWord ++ tailWord_2772500).sum := by decide
  have hdescent : baseEnd_2772500 < baseStart_2772500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772536 : List Nat := [2, 1, 2, 1, 4, 2, 1, 3, 2, 2, 3]
def baseStart_2772536 : Nat := 118140960795 + 2772536 * 2 ^ 59
def prefixEnd_2772536 : Nat := 4983230072969 + 3 ^ 40 * 2772536 * 2
def baseEnd_2772536 : Nat := 1423643599894069673849345

theorem tailTrace_2772536 : CollatzResearch.WordTrace tailWord_2772536 prefixEnd_2772536 1423643599894069673849345 := by
  unfold tailWord_2772536
  simp only [CollatzResearch.WordTrace]
  refine ⟨50561347741791529147868731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67415130322388705530491641 50561347741791529147868731)
  ·
    refine ⟨75842021612687293721803097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50561347741791529147868731 75842021612687293721803097)
    ·
      refine ⟨56881516209515470291352323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75842021612687293721803097 56881516209515470291352323)
      ·
        refine ⟨85322274314273205437028485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56881516209515470291352323 85322274314273205437028485)
        ·
          refine ⟨15997926433926226019442841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85322274314273205437028485 15997926433926226019442841)
          ·
            refine ⟨11998444825444669514582131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15997926433926226019442841 11998444825444669514582131)
            ·
              refine ⟨17997667238167004271873197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11998444825444669514582131 17997667238167004271873197)
              ·
                refine ⟨6749125214312626601952449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17997667238167004271873197 6749125214312626601952449)
                ·
                  refine ⟨5061843910734469951464337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6749125214312626601952449 5061843910734469951464337)
                  ·
                    refine ⟨3796382933050852463598253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5061843910734469951464337 3796382933050852463598253)
                    ·
                      refine ⟨1423643599894069673849345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3796382933050852463598253 1423643599894069673849345)
                      ·
                        rfl

theorem cell23_2772536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 2, 2, 3].length) (baseStart_2772536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772536 prefixEnd_2772536 := by exact prefixLift 2772536
  have htrace : WordTrace (prefixWord ++ tailWord_2772536) baseStart_2772536 baseEnd_2772536 := by
    simpa [prefixWord, tailWord_2772536, baseEnd_2772536] using wordTrace_append hprefix tailTrace_2772536
  have hstable : (prefixWord ++ tailWord_2772536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772536).length < 2 ^ (prefixWord ++ tailWord_2772536).sum := by decide
  have hdescent : baseEnd_2772536 < baseStart_2772536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772556 : List Nat := [2, 2, 1, 3, 1, 4, 2, 2, 6]
def baseStart_2772556 : Nat := 118140960795 + 2772556 * 2 ^ 59
def prefixEnd_2772556 : Nat := 4983230072969 + 3 ^ 40 * 2772556 * 2
def baseEnd_2772556 : Nat := 158183763278573288399917

theorem tailTrace_2772556 : CollatzResearch.WordTrace tailWord_2772556 prefixEnd_2772556 158183763278573288399917 := by
  unfold tailWord_2772556
  simp only [CollatzResearch.WordTrace]
  refine ⟨50561712471755300855732761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67415616629007067807643681 50561712471755300855732761)
  ·
    refine ⟨37921284353816475641799571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50561712471755300855732761 37921284353816475641799571)
    ·
      refine ⟨56881926530724713462699357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37921284353816475641799571 56881926530724713462699357)
      ·
        refine ⟨21330722449021767548512259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56881926530724713462699357 21330722449021767548512259)
        ·
          refine ⟨31996083673532651322768389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21330722449021767548512259 31996083673532651322768389)
          ·
            refine ⟨5999265688787372123019073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31996083673532651322768389 5999265688787372123019073)
            ·
              refine ⟨4499449266590529092264305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5999265688787372123019073 4499449266590529092264305)
              ·
                refine ⟨3374586949942896819198229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4499449266590529092264305 3374586949942896819198229)
                ·
                  refine ⟨158183763278573288399917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3374586949942896819198229 158183763278573288399917)
                  ·
                    rfl

theorem cell23_2772556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 6].length) (baseStart_2772556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772556 prefixEnd_2772556 := by exact prefixLift 2772556
  have htrace : WordTrace (prefixWord ++ tailWord_2772556) baseStart_2772556 baseEnd_2772556 := by
    simpa [prefixWord, tailWord_2772556, baseEnd_2772556] using wordTrace_append hprefix tailTrace_2772556
  have hstable : (prefixWord ++ tailWord_2772556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772556).length < 2 ^ (prefixWord ++ tailWord_2772556).sum := by decide
  have hdescent : baseEnd_2772556 < baseStart_2772556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772576 : List Nat := [2, 1, 1, 3, 2, 1, 1, 4, 1, 5, 2]
def baseStart_2772576 : Nat := 118140960795 + 2772576 * 2 ^ 59
def prefixEnd_2772576 : Nat := 4983230072969 + 3 ^ 40 * 2772576 * 2
def baseEnd_2772576 : Nat := 1423664139120249517349161

theorem tailTrace_2772576 : CollatzResearch.WordTrace tailWord_2772576 prefixEnd_2772576 1423664139120249517349161 := by
  unfold tailWord_2772576
  simp only [CollatzResearch.WordTrace]
  refine ⟨50562077201719072563596791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67416102935625430084795721 50562077201719072563596791)
  ·
    refine ⟨75843115802578608845395187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50562077201719072563596791 75843115802578608845395187)
    ·
      refine ⟨113764673703867913268092781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75843115802578608845395187 113764673703867913268092781)
      ·
        refine ⟨42661752638950467475534793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113764673703867913268092781 42661752638950467475534793)
        ·
          refine ⟨31996314479212850606651095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42661752638950467475534793 31996314479212850606651095)
          ·
            refine ⟨47994471718819275909976643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31996314479212850606651095 47994471718819275909976643)
            ·
              refine ⟨71991707578228913864964965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47994471718819275909976643 71991707578228913864964965)
              ·
                refine ⟨13498445170917921349680931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71991707578228913864964965 13498445170917921349680931)
                ·
                  refine ⟨20247667756376882024521397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13498445170917921349680931 20247667756376882024521397)
                  ·
                    refine ⟨1898218852160332689798881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20247667756376882024521397 1898218852160332689798881)
                    ·
                      refine ⟨1423664139120249517349161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1898218852160332689798881 1423664139120249517349161)
                      ·
                        rfl

theorem cell23_2772576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 1, 5, 2].length) (baseStart_2772576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772576 prefixEnd_2772576 := by exact prefixLift 2772576
  have htrace : WordTrace (prefixWord ++ tailWord_2772576) baseStart_2772576 baseEnd_2772576 := by
    simpa [prefixWord, tailWord_2772576, baseEnd_2772576] using wordTrace_append hprefix tailTrace_2772576
  have hstable : (prefixWord ++ tailWord_2772576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772576).length < 2 ^ (prefixWord ++ tailWord_2772576).sum := by decide
  have hdescent : baseEnd_2772576 < baseStart_2772576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772586 : List Nat := [3, 1, 3, 2, 1, 2, 2, 1, 3, 5]
def baseStart_2772586 : Nat := 118140960795 + 2772586 * 2 ^ 59
def prefixEnd_2772586 : Nat := 4983230072969 + 3 ^ 40 * 2772586 * 2
def baseEnd_2772586 : Nat := 474556424642264826074705

theorem tailTrace_2772586 : CollatzResearch.WordTrace tailWord_2772586 prefixEnd_2772586 474556424642264826074705 := by
  unfold tailWord_2772586
  simp only [CollatzResearch.WordTrace]
  refine ⟨25281129783350479208764403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67416346088934611223371741 25281129783350479208764403)
  ·
    refine ⟨37921694675025718813146605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25281129783350479208764403 37921694675025718813146605)
    ·
      refine ⟨14220635503134644554929977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37921694675025718813146605 14220635503134644554929977)
      ·
        refine ⟨10665476627350983416197483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14220635503134644554929977 10665476627350983416197483)
        ·
          refine ⟨15998214941026475124296225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10665476627350983416197483 15998214941026475124296225)
          ·
            refine ⟨11998661205769856343222169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15998214941026475124296225 11998661205769856343222169)
            ·
              refine ⟨8998995904327392257416627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11998661205769856343222169 8998995904327392257416627)
              ·
                refine ⟨13498493856491088386124941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8998995904327392257416627 13498493856491088386124941)
                ·
                  refine ⟨5061935196184158144796853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13498493856491088386124941 5061935196184158144796853)
                  ·
                    refine ⟨474556424642264826074705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5061935196184158144796853 474556424642264826074705)
                    ·
                      rfl

theorem cell23_2772586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_2772586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772586 prefixEnd_2772586 := by exact prefixLift 2772586
  have htrace : WordTrace (prefixWord ++ tailWord_2772586) baseStart_2772586 baseEnd_2772586 := by
    simpa [prefixWord, tailWord_2772586, baseEnd_2772586] using wordTrace_append hprefix tailTrace_2772586
  have hstable : (prefixWord ++ tailWord_2772586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772586).length < 2 ^ (prefixWord ++ tailWord_2772586).sum := by decide
  have hdescent : baseEnd_2772586 < baseStart_2772586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772619 : List Nat := [1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 6]
def baseStart_2772619 : Nat := 118140960795 + 2772619 * 2 ^ 59
def prefixEnd_2772619 : Nat := 4983230072969 + 3 ^ 40 * 2772619 * 2
def baseEnd_2772619 : Nat := 1423686218788392849111463

theorem tailTrace_2772619 : CollatzResearch.WordTrace tailWord_2772619 prefixEnd_2772619 1423686218788392849111463 := by
  unfold tailWord_2772619
  simp only [CollatzResearch.WordTrace]
  refine ⟨101125722742282363471008911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67417148494854908980672607 101125722742282363471008911)
  ·
    refine ⟨151688584113423545206513367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101125722742282363471008911 151688584113423545206513367)
    ·
      refine ⟨227532876170135317809770051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151688584113423545206513367 227532876170135317809770051)
      ·
        refine ⟨341299314255202976714655077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227532876170135317809770051 341299314255202976714655077)
        ·
          refine ⟨63993621422850558133997827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 341299314255202976714655077 63993621422850558133997827)
          ·
            refine ⟨95990432134275837200996741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63993621422850558133997827 95990432134275837200996741)
            ·
              refine ⟨17998206025176719475186889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95990432134275837200996741 17998206025176719475186889)
              ·
                refine ⟨13498654518882539606390167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17998206025176719475186889 13498654518882539606390167)
                ·
                  refine ⟨20247981778323809409585251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13498654518882539606390167 20247981778323809409585251)
                  ·
                    refine ⟨30371972667485714114377877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20247981778323809409585251 30371972667485714114377877)
                    ·
                      refine ⟨1423686218788392849111463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30371972667485714114377877 1423686218788392849111463)
                      ·
                        rfl

theorem cell23_2772619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 6].length) (baseStart_2772619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772619 prefixEnd_2772619 := by exact prefixLift 2772619
  have htrace : WordTrace (prefixWord ++ tailWord_2772619) baseStart_2772619 baseEnd_2772619 := by
    simpa [prefixWord, tailWord_2772619, baseEnd_2772619] using wordTrace_append hprefix tailTrace_2772619
  have hstable : (prefixWord ++ tailWord_2772619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772619).length < 2 ^ (prefixWord ++ tailWord_2772619).sum := by decide
  have hdescent : baseEnd_2772619 < baseStart_2772619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772640 : List Nat := [2, 1, 1, 4, 3, 1, 2, 2, 3, 2, 2]
def baseStart_2772640 : Nat := 118140960795 + 2772640 * 2 ^ 59
def prefixEnd_2772640 : Nat := 4983230072969 + 3 ^ 40 * 2772640 * 2
def baseEnd_2772640 : Nat := 1423697001882137266948867

theorem tailTrace_2772640 : CollatzResearch.WordTrace tailWord_2772640 prefixEnd_2772640 1423697001882137266948867 := by
  unfold tailWord_2772640
  simp only [CollatzResearch.WordTrace]
  refine ⟨50563244337603142028761687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67417659116804189371682249 50563244337603142028761687)
  ·
    refine ⟨75844866506404713043142531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50563244337603142028761687 75844866506404713043142531)
    ·
      refine ⟨113767299759607069564713797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75844866506404713043142531 113767299759607069564713797)
      ·
        refine ⟨21331368704926325543383837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113767299759607069564713797 21331368704926325543383837)
        ·
          refine ⟨7999263264347372078768939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21331368704926325543383837 7999263264347372078768939)
          ·
            refine ⟨11998894896521058118153409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7999263264347372078768939 11998894896521058118153409)
            ·
              refine ⟨8999171172390793588615057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11998894896521058118153409 8999171172390793588615057)
              ·
                refine ⟨6749378379293095191461293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8999171172390793588615057 6749378379293095191461293)
                ·
                  refine ⟨2531016892234910696797985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6749378379293095191461293 2531016892234910696797985)
                  ·
                    refine ⟨1898262669176183022598489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2531016892234910696797985 1898262669176183022598489)
                    ·
                      refine ⟨1423697001882137266948867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1898262669176183022598489 1423697001882137266948867)
                      ·
                        rfl

theorem cell23_2772640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_2772640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772640 prefixEnd_2772640 := by exact prefixLift 2772640
  have htrace : WordTrace (prefixWord ++ tailWord_2772640) baseStart_2772640 baseEnd_2772640 := by
    simpa [prefixWord, tailWord_2772640, baseEnd_2772640] using wordTrace_append hprefix tailTrace_2772640
  have hstable : (prefixWord ++ tailWord_2772640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772640).length < 2 ^ (prefixWord ++ tailWord_2772640).sum := by decide
  have hdescent : baseEnd_2772640 < baseStart_2772640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772643 : List Nat := [1, 1, 1, 4, 1, 1, 6, 2, 1, 2, 3]
def baseStart_2772643 : Nat := 118140960795 + 2772643 * 2 ^ 59
def prefixEnd_2772643 : Nat := 4983230072969 + 3 ^ 40 * 2772643 * 2
def baseEnd_2772643 : Nat := 1423698542324100755211353

theorem tailTrace_2772643 : CollatzResearch.WordTrace tailWord_2772643 prefixEnd_2772643 1423698542324100755211353 := by
  unfold tailWord_2772643
  simp only [CollatzResearch.WordTrace]
  refine ⟨101126598094195415569882583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67417732062796943713255055 101126598094195415569882583)
  ·
    refine ⟨151689897141293123354823875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101126598094195415569882583 151689897141293123354823875)
    ·
      refine ⟨227534845711939685032235813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151689897141293123354823875 227534845711939685032235813)
      ·
        refine ⟨42662783570988690943544215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 227534845711939685032235813 42662783570988690943544215)
        ·
          refine ⟨63994175356483036415316323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42662783570988690943544215 63994175356483036415316323)
          ·
            refine ⟨95991263034724554622974485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63994175356483036415316323 95991263034724554622974485)
            ·
              refine ⟨4499590454752713497951929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 95991263034724554622974485 4499590454752713497951929)
              ·
                refine ⟨3374692841064535123463947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4499590454752713497951929 3374692841064535123463947)
                ·
                  refine ⟨5062039261596802685195921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3374692841064535123463947 5062039261596802685195921)
                  ·
                    refine ⟨3796529446197602013896941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5062039261596802685195921 3796529446197602013896941)
                    ·
                      refine ⟨1423698542324100755211353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3796529446197602013896941 1423698542324100755211353)
                      ·
                        rfl

theorem cell23_2772643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_2772643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772643 prefixEnd_2772643 := by exact prefixLift 2772643
  have htrace : WordTrace (prefixWord ++ tailWord_2772643) baseStart_2772643 baseEnd_2772643 := by
    simpa [prefixWord, tailWord_2772643, baseEnd_2772643] using wordTrace_append hprefix tailTrace_2772643
  have hstable : (prefixWord ++ tailWord_2772643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772643).length < 2 ^ (prefixWord ++ tailWord_2772643).sum := by decide
  have hdescent : baseEnd_2772643 < baseStart_2772643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772656 : List Nat := [2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 3]
def baseStart_2772656 : Nat := 118140960795 + 2772656 * 2 ^ 59
def prefixEnd_2772656 : Nat := 4983230072969 + 3 ^ 40 * 2772656 * 2
def baseEnd_2772656 : Nat := 1423705217572609204348793

theorem tailTrace_2772656 : CollatzResearch.WordTrace tailWord_2772656 prefixEnd_2772656 1423705217572609204348793 := by
  unfold tailWord_2772656
  simp only [CollatzResearch.WordTrace]
  refine ⟨50563536121574159395052911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67418048162098879193403881 50563536121574159395052911)
  ·
    refine ⟨75845304182361239092579367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50563536121574159395052911 75845304182361239092579367)
    ·
      refine ⟨113767956273541858638869051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75845304182361239092579367 113767956273541858638869051)
      ·
        refine ⟨170651934410312787958303577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113767956273541858638869051 170651934410312787958303577)
        ·
          refine ⟨127988950807734590968727683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170651934410312787958303577 127988950807734590968727683)
          ·
            refine ⟨191983426211601886453091525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127988950807734590968727683 191983426211601886453091525)
            ·
              refine ⟨35996892414675353709954661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 191983426211601886453091525 35996892414675353709954661)
              ·
                refine ⟨6749417327751628820616499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35996892414675353709954661 6749417327751628820616499)
                ·
                  refine ⟨10124125991627443230924749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6749417327751628820616499 10124125991627443230924749)
                  ·
                    refine ⟨3796547246860291211596781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10124125991627443230924749 3796547246860291211596781)
                    ·
                      refine ⟨1423705217572609204348793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3796547246860291211596781 1423705217572609204348793)
                      ·
                        rfl

theorem cell23_2772656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 3].length) (baseStart_2772656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772656 prefixEnd_2772656 := by exact prefixLift 2772656
  have htrace : WordTrace (prefixWord ++ tailWord_2772656) baseStart_2772656 baseEnd_2772656 := by
    simpa [prefixWord, tailWord_2772656, baseEnd_2772656] using wordTrace_append hprefix tailTrace_2772656
  have hstable : (prefixWord ++ tailWord_2772656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772656).length < 2 ^ (prefixWord ++ tailWord_2772656).sum := by decide
  have hdescent : baseEnd_2772656 < baseStart_2772656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772676 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 2, 7]
def baseStart_2772676 : Nat := 118140960795 + 2772676 * 2 ^ 59
def prefixEnd_2772676 : Nat := 4983230072969 + 3 ^ 40 * 2772676 * 2
def baseEnd_2772676 : Nat := 474571829061899708699567

theorem tailTrace_2772676 : CollatzResearch.WordTrace tailWord_2772676 prefixEnd_2772676 474571829061899708699567 := by
  unfold tailWord_2772676
  simp only [CollatzResearch.WordTrace]
  refine ⟨50563900851537931102916941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67418534468717241470555921 50563900851537931102916941)
  ·
    refine ⟨18961462819326724163593853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50563900851537931102916941 18961462819326724163593853)
    ·
      refine ⟨7110548557247521561347695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18961462819326724163593853 7110548557247521561347695)
      ·
        refine ⟨10665822835871282342021543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7110548557247521561347695 10665822835871282342021543)
        ·
          refine ⟨15998734253806923513032315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10665822835871282342021543 15998734253806923513032315)
          ·
            refine ⟨23998101380710385269548473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15998734253806923513032315 23998101380710385269548473)
            ·
              refine ⟨17998576035532788952161355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23998101380710385269548473 17998576035532788952161355)
              ·
                refine ⟨26997864053299183428242033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17998576035532788952161355 26997864053299183428242033)
                ·
                  refine ⟨20248398039974387571181525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26997864053299183428242033 20248398039974387571181525)
                  ·
                    refine ⟨474571829061899708699567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20248398039974387571181525 474571829061899708699567)
                    ·
                      rfl

theorem cell23_2772676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_2772676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772676 prefixEnd_2772676 := by exact prefixLift 2772676
  have htrace : WordTrace (prefixWord ++ tailWord_2772676) baseStart_2772676 baseEnd_2772676 := by
    simpa [prefixWord, tailWord_2772676, baseEnd_2772676] using wordTrace_append hprefix tailTrace_2772676
  have hstable : (prefixWord ++ tailWord_2772676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772676).length < 2 ^ (prefixWord ++ tailWord_2772676).sum := by decide
  have hdescent : baseEnd_2772676 < baseStart_2772676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772684 : List Nat := [2, 2, 1, 5, 3, 1, 2, 1, 2, 4]
def baseStart_2772684 : Nat := 118140960795 + 2772684 * 2 ^ 59
def prefixEnd_2772684 : Nat := 4983230072969 + 3 ^ 40 * 2772684 * 2
def baseEnd_2772684 : Nat := 474573198343645031599555

theorem tailTrace_2772684 : CollatzResearch.WordTrace tailWord_2772684 prefixEnd_2772684 474573198343645031599555 := by
  unfold tailWord_2772684
  simp only [CollatzResearch.WordTrace]
  refine ⟨50564046743523439786062553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67418728991364586381416737 50564046743523439786062553)
  ·
    refine ⟨37923035057642579839546915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50564046743523439786062553 37923035057642579839546915)
    ·
      refine ⟨56884552586463869759320373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37923035057642579839546915 56884552586463869759320373)
      ·
        refine ⟨5332926804980987789936285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56884552586463869759320373 5332926804980987789936285)
        ·
          refine ⟨1999847551867870421226107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5332926804980987789936285 1999847551867870421226107)
          ·
            refine ⟨2999771327801805631839161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1999847551867870421226107 2999771327801805631839161)
            ·
              refine ⟨2249828495851354223879371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2999771327801805631839161 2249828495851354223879371)
              ·
                refine ⟨3374742743777031335819057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2249828495851354223879371 3374742743777031335819057)
                ·
                  refine ⟨2531057057832773501864293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3374742743777031335819057 2531057057832773501864293)
                  ·
                    refine ⟨474573198343645031599555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2531057057832773501864293 474573198343645031599555)
                    ·
                      rfl

theorem cell23_2772684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 2, 4].length) (baseStart_2772684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772684 prefixEnd_2772684 := by exact prefixLift 2772684
  have htrace : WordTrace (prefixWord ++ tailWord_2772684) baseStart_2772684 baseEnd_2772684 := by
    simpa [prefixWord, tailWord_2772684, baseEnd_2772684] using wordTrace_append hprefix tailTrace_2772684
  have hstable : (prefixWord ++ tailWord_2772684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772684).length < 2 ^ (prefixWord ++ tailWord_2772684).sum := by decide
  have hdescent : baseEnd_2772684 < baseStart_2772684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772716 : List Nat := [2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 5]
def baseStart_2772716 : Nat := 118140960795 + 2772716 * 2 ^ 59
def prefixEnd_2772716 : Nat := 4983230072969 + 3 ^ 40 * 2772716 * 2
def baseEnd_2772716 : Nat := 1423736026411878969598517

theorem tailTrace_2772716 : CollatzResearch.WordTrace tailWord_2772716 prefixEnd_2772716 1423736026411878969598517 := by
  unfold tailWord_2772716
  simp only [CollatzResearch.WordTrace]
  refine ⟨50564630311465474518645001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67419507081953966024860001 50564630311465474518645001)
  ·
    refine ⟨37923472733599105888983751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50564630311465474518645001 37923472733599105888983751)
    ·
      refine ⟨56885209100398658833475627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37923472733599105888983751 56885209100398658833475627)
      ·
        refine ⟨85327813650597988250213441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56885209100398658833475627 85327813650597988250213441)
        ·
          refine ⟨63995860237948491187660081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85327813650597988250213441 63995860237948491187660081)
          ·
            refine ⟨47996895178461368390745061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63995860237948491187660081 47996895178461368390745061)
            ·
              refine ⟨8999417845961506573264699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47996895178461368390745061 8999417845961506573264699)
              ·
                refine ⟨13499126768942259859897049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8999417845961506573264699 13499126768942259859897049)
                ·
                  refine ⟨10124345076706694894922787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13499126768942259859897049 10124345076706694894922787)
                  ·
                    refine ⟨15186517615060042342384181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10124345076706694894922787 15186517615060042342384181)
                    ·
                      refine ⟨1423736026411878969598517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15186517615060042342384181 1423736026411878969598517)
                      ·
                        rfl

theorem cell23_2772716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_2772716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772716 prefixEnd_2772716 := by exact prefixLift 2772716
  have htrace : WordTrace (prefixWord ++ tailWord_2772716) baseStart_2772716 baseEnd_2772716 := by
    simpa [prefixWord, tailWord_2772716, baseEnd_2772716] using wordTrace_append hprefix tailTrace_2772716
  have hstable : (prefixWord ++ tailWord_2772716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772716).length < 2 ^ (prefixWord ++ tailWord_2772716).sum := by decide
  have hdescent : baseEnd_2772716 < baseStart_2772716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772724 : List Nat := [2, 6, 1, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_2772724 : Nat := 118140960795 + 2772724 * 2 ^ 59
def prefixEnd_2772724 : Nat := 4983230072969 + 3 ^ 40 * 2772724 * 2
def baseEnd_2772724 : Nat := 1423740134257114938298481

theorem tailTrace_2772724 : CollatzResearch.WordTrace tailWord_2772724 prefixEnd_2772724 1423740134257114938298481 := by
  unfold tailWord_2772724
  simp only [CollatzResearch.WordTrace]
  refine ⟨50564776203450983201790613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67419701604601310935720817 50564776203450983201790613)
  ·
    refine ⟨2370223884536764837583935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50564776203450983201790613 2370223884536764837583935)
    ·
      refine ⟨3555335826805147256375903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2370223884536764837583935 3555335826805147256375903)
      ·
        refine ⟨5333003740207720884563855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3555335826805147256375903 5333003740207720884563855)
        ·
          refine ⟨7999505610311581326845783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5333003740207720884563855 7999505610311581326845783)
          ·
            refine ⟨11999258415467371990268675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7999505610311581326845783 11999258415467371990268675)
            ·
              refine ⟨17998887623201057985403013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11999258415467371990268675 17998887623201057985403013)
              ·
                refine ⟨3374791429350198372263065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17998887623201057985403013 3374791429350198372263065)
                ·
                  refine ⟨2531093572012648779197299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3374791429350198372263065 2531093572012648779197299)
                  ·
                    refine ⟨3796640358018973168795949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2531093572012648779197299 3796640358018973168795949)
                    ·
                      refine ⟨1423740134257114938298481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3796640358018973168795949 1423740134257114938298481)
                      ·
                        rfl

theorem cell23_2772724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_2772724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772724 prefixEnd_2772724 := by exact prefixLift 2772724
  have htrace : WordTrace (prefixWord ++ tailWord_2772724) baseStart_2772724 baseEnd_2772724 := by
    simpa [prefixWord, tailWord_2772724, baseEnd_2772724] using wordTrace_append hprefix tailTrace_2772724
  have hstable : (prefixWord ++ tailWord_2772724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772724).length < 2 ^ (prefixWord ++ tailWord_2772724).sum := by decide
  have hdescent : baseEnd_2772724 < baseStart_2772724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772770 : List Nat := [3, 3, 1, 1, 2, 1, 4, 3, 5]
def baseStart_2772770 : Nat := 118140960795 + 2772770 * 2 ^ 59
def prefixEnd_2772770 : Nat := 4983230072969 + 3 ^ 40 * 2772770 * 2
def baseEnd_2772770 : Nat := 158195972707469084258141

theorem tailTrace_2772770 : CollatzResearch.WordTrace tailWord_2772770 prefixEnd_2772770 158195972707469084258141 := by
  unfold tailWord_2772770
  simp only [CollatzResearch.WordTrace]
  refine ⟨25282807541183829064938941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67420820109823544173170509 25282807541183829064938941)
  ·
    refine ⟨9481052827943935899352103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25282807541183829064938941 9481052827943935899352103)
    ·
      refine ⟨14221579241915903849028155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9481052827943935899352103 14221579241915903849028155)
      ·
        refine ⟨21332368862873855773542233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14221579241915903849028155 21332368862873855773542233)
        ·
          refine ⟨15999276647155391830156675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21332368862873855773542233 15999276647155391830156675)
          ·
            refine ⟨23998914970733087745235013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15999276647155391830156675 23998914970733087745235013)
            ·
              refine ⟨4499796557012453952231565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23998914970733087745235013 4499796557012453952231565)
              ·
                refine ⟨1687423708879670232086837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4499796557012453952231565 1687423708879670232086837)
                ·
                  refine ⟨158195972707469084258141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1687423708879670232086837 158195972707469084258141)
                  ·
                    rfl

theorem cell23_2772770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_2772770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772770 prefixEnd_2772770 := by exact prefixLift 2772770
  have htrace : WordTrace (prefixWord ++ tailWord_2772770) baseStart_2772770 baseEnd_2772770 := by
    simpa [prefixWord, tailWord_2772770, baseEnd_2772770] using wordTrace_append hprefix tailTrace_2772770
  have hstable : (prefixWord ++ tailWord_2772770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772770).length < 2 ^ (prefixWord ++ tailWord_2772770).sum := by decide
  have hdescent : baseEnd_2772770 < baseStart_2772770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772816 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 4]
def baseStart_2772816 : Nat := 118140960795 + 2772816 * 2 ^ 59
def prefixEnd_2772816 : Nat := 4983230072969 + 3 ^ 40 * 2772816 * 2
def baseEnd_2772816 : Nat := 1423787374477328578348057

theorem tailTrace_2772816 : CollatzResearch.WordTrace tailWord_2772816 prefixEnd_2772816 1423787374477328578348057 := by
  unfold tailWord_2772816
  simp only [CollatzResearch.WordTrace]
  refine ⟨50566453961284333057965151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67421938615045777410620201 50566453961284333057965151)
  ·
    refine ⟨75849680941926499586947727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50566453961284333057965151 75849680941926499586947727)
    ·
      refine ⟨113774521412889749380421591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75849680941926499586947727 113774521412889749380421591)
      ·
        refine ⟨170661782119334624070632387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113774521412889749380421591 170661782119334624070632387)
        ·
          refine ⟨255992673179001936105948581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170661782119334624070632387 255992673179001936105948581)
          ·
            refine ⟨47998626221062863019865359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 255992673179001936105948581 47998626221062863019865359)
            ·
              refine ⟨71997939331594294529798039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47998626221062863019865359 71997939331594294529798039)
              ·
                refine ⟨107996908997391441794697059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71997939331594294529798039 107996908997391441794697059)
                ·
                  refine ⟨161995363496087162692045589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107996908997391441794697059 161995363496087162692045589)
                  ·
                    refine ⟨7593532663879085751189637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 161995363496087162692045589 7593532663879085751189637)
                    ·
                      refine ⟨1423787374477328578348057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7593532663879085751189637 1423787374477328578348057)
                      ·
                        rfl

theorem cell23_2772816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 4].length) (baseStart_2772816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772816 prefixEnd_2772816 := by exact prefixLift 2772816
  have htrace : WordTrace (prefixWord ++ tailWord_2772816) baseStart_2772816 baseEnd_2772816 := by
    simpa [prefixWord, tailWord_2772816, baseEnd_2772816] using wordTrace_append hprefix tailTrace_2772816
  have hstable : (prefixWord ++ tailWord_2772816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772816).length < 2 ^ (prefixWord ++ tailWord_2772816).sum := by decide
  have hdescent : baseEnd_2772816 < baseStart_2772816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772826 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 10]
def baseStart_2772826 : Nat := 118140960795 + 2772826 * 2 ^ 59
def prefixEnd_2772826 : Nat := 4983230072969 + 3 ^ 40 * 2772826 * 2
def baseEnd_2772826 : Nat := 158199167698208171024779

theorem tailTrace_2772826 : CollatzResearch.WordTrace tailWord_2772826 prefixEnd_2772826 158199167698208171024779 := by
  unfold tailWord_2772826
  simp only [CollatzResearch.WordTrace]
  refine ⟨25283318163133109455948583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67422181768354958549196221 25283318163133109455948583)
  ·
    refine ⟨37924977244699664183922875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25283318163133109455948583 37924977244699664183922875)
    ·
      refine ⟨56887465867049496275884313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37924977244699664183922875 56887465867049496275884313)
      ·
        refine ⟨42665599400287122206913235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56887465867049496275884313 42665599400287122206913235)
        ·
          refine ⟨63998399100430683310369853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42665599400287122206913235 63998399100430683310369853)
          ·
            refine ⟨23999399662661506241388695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63998399100430683310369853 23999399662661506241388695)
            ·
              refine ⟨35999099493992259362083043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23999399662661506241388695 35999099493992259362083043)
              ·
                refine ⟨53998649240988389043124565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35999099493992259362083043 53998649240988389043124565)
                ·
                  refine ⟨158199167698208171024779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 53998649240988389043124565 158199167698208171024779)
                  ·
                    rfl

theorem cell23_2772826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 10].length) (baseStart_2772826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772826 prefixEnd_2772826 := by exact prefixLift 2772826
  have htrace : WordTrace (prefixWord ++ tailWord_2772826) baseStart_2772826 baseEnd_2772826 := by
    simpa [prefixWord, tailWord_2772826, baseEnd_2772826] using wordTrace_append hprefix tailTrace_2772826
  have hstable : (prefixWord ++ tailWord_2772826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772826).length < 2 ^ (prefixWord ++ tailWord_2772826).sum := by decide
  have hdescent : baseEnd_2772826 < baseStart_2772826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772840 : List Nat := [2, 1, 4, 2, 1, 1, 3, 2, 2, 2, 3]
def baseStart_2772840 : Nat := 118140960795 + 2772840 * 2 ^ 59
def prefixEnd_2772840 : Nat := 4983230072969 + 3 ^ 40 * 2772840 * 2
def baseEnd_2772840 : Nat := 1423799698013036484447947

theorem tailTrace_2772840 : CollatzResearch.WordTrace tailWord_2772840 prefixEnd_2772840 1423799698013036484447947 := by
  unfold tailWord_2772840
  simp only [CollatzResearch.WordTrace]
  refine ⟨50566891637240859107401987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67422522182987812143202649 50566891637240859107401987)
  ·
    refine ⟨75850337455861288661102981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50566891637240859107401987 75850337455861288661102981)
    ·
      refine ⟨14221938272973991623956809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75850337455861288661102981 14221938272973991623956809)
      ·
        refine ⟨10666453704730493717967607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14221938272973991623956809 10666453704730493717967607)
        ·
          refine ⟨15999680557095740576951411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10666453704730493717967607 15999680557095740576951411)
          ·
            refine ⟨23999520835643610865427117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15999680557095740576951411 23999520835643610865427117)
            ·
              refine ⟨8999820313366354074535169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23999520835643610865427117 8999820313366354074535169)
              ·
                refine ⟨6749865235024765555901377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8999820313366354074535169 6749865235024765555901377)
                ·
                  refine ⟨5062398926268574166926033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6749865235024765555901377 5062398926268574166926033)
                  ·
                    refine ⟨3796799194701430625194525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5062398926268574166926033 3796799194701430625194525)
                    ·
                      refine ⟨1423799698013036484447947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3796799194701430625194525 1423799698013036484447947)
                      ·
                        rfl

theorem cell23_2772840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_2772840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772840 prefixEnd_2772840 := by exact prefixLift 2772840
  have htrace : WordTrace (prefixWord ++ tailWord_2772840) baseStart_2772840 baseEnd_2772840 := by
    simpa [prefixWord, tailWord_2772840, baseEnd_2772840] using wordTrace_append hprefix tailTrace_2772840
  have hstable : (prefixWord ++ tailWord_2772840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772840).length < 2 ^ (prefixWord ++ tailWord_2772840).sum := by decide
  have hdescent : baseEnd_2772840 < baseStart_2772840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772873 : List Nat := [1, 2, 1, 1, 5, 1, 3, 1, 3, 5]
def baseStart_2772873 : Nat := 118140960795 + 2772873 * 2 ^ 59
def prefixEnd_2772873 : Nat := 4983230072969 + 3 ^ 40 * 2772873 * 2
def baseEnd_2772873 : Nat := 474605547624878285111765

theorem tailTrace_2772873 : CollatzResearch.WordTrace tailWord_2772873 prefixEnd_2772873 474605547624878285111765 := by
  unfold tailWord_2772873
  simp only [CollatzResearch.WordTrace]
  refine ⟨101134986883362164850755273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67423324588908109900503515 101134986883362164850755273)
  ·
    refine ⟨75851240162521623638066455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101134986883362164850755273 75851240162521623638066455)
    ·
      refine ⟨113776860243782435457099683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75851240162521623638066455 113776860243782435457099683)
      ·
        refine ⟨170665290365673653185649525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113776860243782435457099683 170665290365673653185649525)
        ·
          refine ⟨15999870971781904986154643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 170665290365673653185649525 15999870971781904986154643)
          ·
            refine ⟨23999806457672857479231965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15999870971781904986154643 23999806457672857479231965)
            ·
              refine ⟨8999927421627321554711987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23999806457672857479231965 8999927421627321554711987)
              ·
                refine ⟨13499891132440982332067981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8999927421627321554711987 13499891132440982332067981)
                ·
                  refine ⟨5062459174665368374525493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13499891132440982332067981 5062459174665368374525493)
                  ·
                    refine ⟨474605547624878285111765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5062459174665368374525493 474605547624878285111765)
                    ·
                      rfl

theorem cell23_2772873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 5].length) (baseStart_2772873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772873 prefixEnd_2772873 := by exact prefixLift 2772873
  have htrace : WordTrace (prefixWord ++ tailWord_2772873) baseStart_2772873 baseEnd_2772873 := by
    simpa [prefixWord, tailWord_2772873, baseEnd_2772873] using wordTrace_append hprefix tailTrace_2772873
  have hstable : (prefixWord ++ tailWord_2772873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772873).length < 2 ^ (prefixWord ++ tailWord_2772873).sum := by decide
  have hdescent : baseEnd_2772873 < baseStart_2772873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772880 : List Nat := [2, 1, 1, 1, 1, 1, 2, 7, 2, 3, 2]
def baseStart_2772880 : Nat := 118140960795 + 2772880 * 2 ^ 59
def prefixEnd_2772880 : Nat := 4983230072969 + 3 ^ 40 * 2772880 * 2
def baseEnd_2772880 : Nat := 1423820237239216327947763

theorem tailTrace_2772880 : CollatzResearch.WordTrace tailWord_2772880 prefixEnd_2772880 1423820237239216327947763 := by
  unfold tailWord_2772880
  simp only [CollatzResearch.WordTrace]
  refine ⟨50567621097168402523130047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67423494796224536697506729 50567621097168402523130047)
  ·
    refine ⟨75851431645752603784695071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50567621097168402523130047 75851431645752603784695071)
    ·
      refine ⟨113777147468628905677042607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75851431645752603784695071 113777147468628905677042607)
      ·
        refine ⟨170665721202943358515563911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113777147468628905677042607 170665721202943358515563911)
        ·
          refine ⟨255998581804415037773345867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170665721202943358515563911 255998581804415037773345867)
          ·
            refine ⟨383997872706622556660018801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255998581804415037773345867 383997872706622556660018801)
            ·
              refine ⟨287998404529966917495014101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383997872706622556660018801 287998404529966917495014101)
              ·
                refine ⟨6749962606171099628789393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 287998404529966917495014101 6749962606171099628789393)
                ·
                  refine ⟨5062471954628324721592045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6749962606171099628789393 5062471954628324721592045)
                  ·
                    refine ⟨1898426982985621770597017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5062471954628324721592045 1898426982985621770597017)
                    ·
                      refine ⟨1423820237239216327947763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1898426982985621770597017 1423820237239216327947763)
                      ·
                        rfl

theorem cell23_2772880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 2, 3, 2].length) (baseStart_2772880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772880 prefixEnd_2772880 := by exact prefixLift 2772880
  have htrace : WordTrace (prefixWord ++ tailWord_2772880) baseStart_2772880 baseEnd_2772880 := by
    simpa [prefixWord, tailWord_2772880, baseEnd_2772880] using wordTrace_append hprefix tailTrace_2772880
  have hstable : (prefixWord ++ tailWord_2772880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772880).length < 2 ^ (prefixWord ++ tailWord_2772880).sum := by decide
  have hdescent : baseEnd_2772880 < baseStart_2772880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772894 : List Nat := [4, 3, 1, 3, 1, 1, 2, 2, 6]
def baseStart_2772894 : Nat := 118140960795 + 2772894 * 2 ^ 59
def prefixEnd_2772894 : Nat := 4983230072969 + 3 ^ 40 * 2772894 * 2
def baseEnd_2772894 : Nat := 158203047329819919241411

theorem tailTrace_2772894 : CollatzResearch.WordTrace tailWord_2772894 prefixEnd_2772894 158203047329819919241411 := by
  unfold tailWord_2772894
  simp only [CollatzResearch.WordTrace]
  refine ⟨12641969102035760679658717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67423835210857390291513157 12641969102035760679658717)
  ·
    refine ⟨4740738413263410254872019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12641969102035760679658717 4740738413263410254872019)
    ·
      refine ⟨7111107619895115382308029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4740738413263410254872019 7111107619895115382308029)
      ·
        refine ⟨2666665357460668268365511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7111107619895115382308029 2666665357460668268365511)
        ·
          refine ⟨3999998036191002402548267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2666665357460668268365511 3999998036191002402548267)
          ·
            refine ⟨5999997054286503603822401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3999998036191002402548267 5999997054286503603822401)
            ·
              refine ⟨4499997790714877702866801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5999997054286503603822401 4499997790714877702866801)
              ·
                refine ⟨3374998343036158277150101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4499997790714877702866801 3374998343036158277150101)
                ·
                  refine ⟨158203047329819919241411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3374998343036158277150101 158203047329819919241411)
                  ·
                    rfl

theorem cell23_2772894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_2772894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772894 prefixEnd_2772894 := by exact prefixLift 2772894
  have htrace : WordTrace (prefixWord ++ tailWord_2772894) baseStart_2772894 baseEnd_2772894 := by
    simpa [prefixWord, tailWord_2772894, baseEnd_2772894] using wordTrace_append hprefix tailTrace_2772894
  have hstable : (prefixWord ++ tailWord_2772894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772894).length < 2 ^ (prefixWord ++ tailWord_2772894).sum := by decide
  have hdescent : baseEnd_2772894 < baseStart_2772894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772898 : List Nat := [3, 3, 1, 2, 4, 1, 2, 2, 1, 4]
def baseStart_2772898 : Nat := 118140960795 + 2772898 * 2 ^ 59
def prefixEnd_2772898 : Nat := 4983230072969 + 3 ^ 40 * 2772898 * 2
def baseEnd_2772898 : Nat := 474609826630332419174227

theorem tailTrace_2772898 : CollatzResearch.WordTrace tailWord_2772898 prefixEnd_2772898 474609826630332419174227 := by
  unfold tailWord_2772898
  simp only [CollatzResearch.WordTrace]
  refine ⟨25283974677067898530103837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67423932472181062746943565 25283974677067898530103837)
  ·
    refine ⟨9481490503900461948788939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25283974677067898530103837 9481490503900461948788939)
    ·
      refine ⟨14222235755850692923183409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9481490503900461948788939 14222235755850692923183409)
      ·
        refine ⟨10666676816888019692387557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14222235755850692923183409 10666676816888019692387557)
        ·
          refine ⟨2000001903166503692322667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10666676816888019692387557 2000001903166503692322667)
          ·
            refine ⟨3000002854749755538484001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2000001903166503692322667 3000002854749755538484001)
            ·
              refine ⟨2250002141062316653863001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3000002854749755538484001 2250002141062316653863001)
              ·
                refine ⟨1687501605796737490397251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2250002141062316653863001 1687501605796737490397251)
                ·
                  refine ⟨2531252408695106235595877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1687501605796737490397251 2531252408695106235595877)
                  ·
                    refine ⟨474609826630332419174227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2531252408695106235595877 474609826630332419174227)
                    ·
                      rfl

theorem cell23_2772898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_2772898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772898 prefixEnd_2772898 := by exact prefixLift 2772898
  have htrace : WordTrace (prefixWord ++ tailWord_2772898) baseStart_2772898 baseEnd_2772898 := by
    simpa [prefixWord, tailWord_2772898, baseEnd_2772898] using wordTrace_append hprefix tailTrace_2772898
  have hstable : (prefixWord ++ tailWord_2772898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772898).length < 2 ^ (prefixWord ++ tailWord_2772898).sum := by decide
  have hdescent : baseEnd_2772898 < baseStart_2772898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772920 : List Nat := [2, 1, 2, 1, 2, 3, 1, 5, 2, 4]
def baseStart_2772920 : Nat := 118140960795 + 2772920 * 2 ^ 59
def prefixEnd_2772920 : Nat := 4983230072969 + 3 ^ 40 * 2772920 * 2
def baseEnd_2772920 : Nat := 474613592155132057149193

theorem tailTrace_2772920 : CollatzResearch.WordTrace tailWord_2772920 prefixEnd_2772920 474613592155132057149193 := by
  unfold tailWord_2772920
  simp only [CollatzResearch.WordTrace]
  refine ⟨50568350557095945938858107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67424467409461261251810809 50568350557095945938858107)
  ·
    refine ⟨75852525835643918908287161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50568350557095945938858107 75852525835643918908287161)
    ·
      refine ⟨56889394376732939181215371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75852525835643918908287161 56889394376732939181215371)
      ·
        refine ⟨85334091565099408771823057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56889394376732939181215371 85334091565099408771823057)
        ·
          refine ⟨64000568673824556578867293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85334091565099408771823057 64000568673824556578867293)
          ·
            refine ⟨24000213252684208717075235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64000568673824556578867293 24000213252684208717075235)
            ·
              refine ⟨36000319879026313075612853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24000213252684208717075235 36000319879026313075612853)
              ·
                refine ⟨3375029988658716850838705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36000319879026313075612853 3375029988658716850838705)
                ·
                  refine ⟨2531272491494037638129029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3375029988658716850838705 2531272491494037638129029)
                  ·
                    refine ⟨474613592155132057149193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2531272491494037638129029 474613592155132057149193)
                    ·
                      rfl

theorem cell23_2772920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 2, 4].length) (baseStart_2772920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772920 prefixEnd_2772920 := by exact prefixLift 2772920
  have htrace : WordTrace (prefixWord ++ tailWord_2772920) baseStart_2772920 baseEnd_2772920 := by
    simpa [prefixWord, tailWord_2772920, baseEnd_2772920] using wordTrace_append hprefix tailTrace_2772920
  have hstable : (prefixWord ++ tailWord_2772920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772920).length < 2 ^ (prefixWord ++ tailWord_2772920).sum := by decide
  have hdescent : baseEnd_2772920 < baseStart_2772920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772923 : List Nat := [1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 4]
def baseStart_2772923 : Nat := 118140960795 + 2772923 * 2 ^ 59
def prefixEnd_2772923 : Nat := 4983230072969 + 3 ^ 40 * 2772923 * 2
def baseEnd_2772923 : Nat := 1423842316907359659710065

theorem tailTrace_2772923 : CollatzResearch.WordTrace tailWord_2772923 prefixEnd_2772923 1423842316907359659710065 := by
  unfold tailWord_2772923
  simp only [CollatzResearch.WordTrace]
  refine ⟨101136810533181023390075423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67424540355454015593383615 101136810533181023390075423)
  ·
    refine ⟨151705215799771535085113135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101136810533181023390075423 151705215799771535085113135)
    ·
      refine ⟨227557823699657302627669703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151705215799771535085113135 227557823699657302627669703)
      ·
        refine ⟨341336735549485953941504555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227557823699657302627669703 341336735549485953941504555)
        ·
          refine ⟨512005103324228930912256833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341336735549485953941504555 512005103324228930912256833)
          ·
            refine ⟨384003827493171698184192625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 512005103324228930912256833 384003827493171698184192625)
            ·
              refine ⟨288002870619878773638144469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 384003827493171698184192625 288002870619878773638144469)
              ·
                refine ⟨6750067280153408757144011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 288002870619878773638144469 6750067280153408757144011)
                ·
                  refine ⟨10125100920230113135716017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6750067280153408757144011 10125100920230113135716017)
                  ·
                    refine ⟨7593825690172584851787013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10125100920230113135716017 7593825690172584851787013)
                    ·
                      refine ⟨1423842316907359659710065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7593825690172584851787013 1423842316907359659710065)
                      ·
                        rfl

theorem cell23_2772923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 4].length) (baseStart_2772923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772923 prefixEnd_2772923 := by exact prefixLift 2772923
  have htrace : WordTrace (prefixWord ++ tailWord_2772923) baseStart_2772923 baseEnd_2772923 := by
    simpa [prefixWord, tailWord_2772923, baseEnd_2772923] using wordTrace_append hprefix tailTrace_2772923
  have hstable : (prefixWord ++ tailWord_2772923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772923).length < 2 ^ (prefixWord ++ tailWord_2772923).sum := by decide
  have hdescent : baseEnd_2772923 < baseStart_2772923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772927 : List Nat := [1, 1, 2, 2, 2, 1, 5, 2, 3, 2, 2]
def baseStart_2772927 : Nat := 118140960795 + 2772927 * 2 ^ 59
def prefixEnd_2772927 : Nat := 4983230072969 + 3 ^ 40 * 2772927 * 2
def baseEnd_2772927 : Nat := 1423844370829977644060047

theorem tailTrace_2772927 : CollatzResearch.WordTrace tailWord_2772927 prefixEnd_2772927 1423844370829977644060047 := by
  unfold tailWord_2772927
  simp only [CollatzResearch.WordTrace]
  refine ⟨101136956425166532073221035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67424637616777688048814023 101136956425166532073221035)
  ·
    refine ⟨151705434637749798109831553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101136956425166532073221035 151705434637749798109831553)
    ·
      refine ⟨113779075978312348582373665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151705434637749798109831553 113779075978312348582373665)
      ·
        refine ⟨85334306983734261436780249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113779075978312348582373665 85334306983734261436780249)
        ·
          refine ⟨64000730237800696077585187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85334306983734261436780249 64000730237800696077585187)
          ·
            refine ⟨96001095356701044116377781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64000730237800696077585187 96001095356701044116377781)
            ·
              refine ⟨9000102689690722885910417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96001095356701044116377781 9000102689690722885910417)
              ·
                refine ⟨6750077017268042164432813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9000102689690722885910417 6750077017268042164432813)
                ·
                  refine ⟨2531278881475515811662305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6750077017268042164432813 2531278881475515811662305)
                  ·
                    refine ⟨1898459161106636858746729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2531278881475515811662305 1898459161106636858746729)
                    ·
                      refine ⟨1423844370829977644060047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1898459161106636858746729 1423844370829977644060047)
                      ·
                        rfl

theorem cell23_2772927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3, 2, 2].length) (baseStart_2772927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772927 prefixEnd_2772927 := by exact prefixLift 2772927
  have htrace : WordTrace (prefixWord ++ tailWord_2772927) baseStart_2772927 baseEnd_2772927 := by
    simpa [prefixWord, tailWord_2772927, baseEnd_2772927] using wordTrace_append hprefix tailTrace_2772927
  have hstable : (prefixWord ++ tailWord_2772927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772927).length < 2 ^ (prefixWord ++ tailWord_2772927).sum := by decide
  have hdescent : baseEnd_2772927 < baseStart_2772927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772940 : List Nat := [2, 2, 1, 4, 1, 2, 2, 2, 1, 2, 4]
def baseStart_2772940 : Nat := 118140960795 + 2772940 * 2 ^ 59
def prefixEnd_2772940 : Nat := 4983230072969 + 3 ^ 40 * 2772940 * 2
def baseEnd_2772940 : Nat := 1423851046078486093197487

theorem tailTrace_2772940 : CollatzResearch.WordTrace tailWord_2772940 prefixEnd_2772940 1423851046078486093197487 := by
  unfold tailWord_2772940
  simp only [CollatzResearch.WordTrace]
  refine ⟨50568715287059717646722137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67424953716079623528962849 50568715287059717646722137)
  ·
    refine ⟨37926536465294788235041603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50568715287059717646722137 37926536465294788235041603)
    ·
      refine ⟨56889804697942182352562405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37926536465294788235041603 56889804697942182352562405)
      ·
        refine ⟨10666838380864159191105451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56889804697942182352562405 10666838380864159191105451)
        ·
          refine ⟨16000257571296238786658177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10666838380864159191105451 16000257571296238786658177)
          ·
            refine ⟨12000193178472179089993633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16000257571296238786658177 12000193178472179089993633)
            ·
              refine ⟨9000144883854134317495225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12000193178472179089993633 9000144883854134317495225)
              ·
                refine ⟨6750108662890600738121419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9000144883854134317495225 6750108662890600738121419)
                ·
                  refine ⟨10125162994335901107182129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6750108662890600738121419 10125162994335901107182129)
                  ·
                    refine ⟨7593872245751925830386597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10125162994335901107182129 7593872245751925830386597)
                    ·
                      refine ⟨1423851046078486093197487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7593872245751925830386597 1423851046078486093197487)
                      ·
                        rfl

theorem cell23_2772940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_2772940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772940 prefixEnd_2772940 := by exact prefixLift 2772940
  have htrace : WordTrace (prefixWord ++ tailWord_2772940) baseStart_2772940 baseEnd_2772940 := by
    simpa [prefixWord, tailWord_2772940, baseEnd_2772940] using wordTrace_append hprefix tailTrace_2772940
  have hstable : (prefixWord ++ tailWord_2772940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772940).length < 2 ^ (prefixWord ++ tailWord_2772940).sum := by decide
  have hdescent : baseEnd_2772940 < baseStart_2772940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772944 : List Nat := [2, 1, 1, 1, 1, 2, 5, 5, 1, 2, 2]
def baseStart_2772944 : Nat := 118140960795 + 2772944 * 2 ^ 59
def prefixEnd_2772944 : Nat := 4983230072969 + 3 ^ 40 * 2772944 * 2
def baseEnd_2772944 : Nat := 1423853100001104077547469

theorem tailTrace_2772944 : CollatzResearch.WordTrace tailWord_2772944 prefixEnd_2772944 1423853100001104077547469 := by
  unfold tailWord_2772944
  simp only [CollatzResearch.WordTrace]
  refine ⟨50568788233052471988294943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67425050977403295984393257 50568788233052471988294943)
  ·
    refine ⟨75853182349578707982442415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50568788233052471988294943 75853182349578707982442415)
    ·
      refine ⟨113779773524368061973663623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75853182349578707982442415 113779773524368061973663623)
      ·
        refine ⟨170669660286552092960495435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113779773524368061973663623 170669660286552092960495435)
        ·
          refine ⟨256004490429828139440743153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170669660286552092960495435 256004490429828139440743153)
          ·
            refine ⟨192003367822371104580557365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256004490429828139440743153 192003367822371104580557365)
            ·
              refine ⟨18000315733347291054427253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 192003367822371104580557365 18000315733347291054427253)
              ·
                refine ⟨1687529600001308536352555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18000315733347291054427253 1687529600001308536352555)
                ·
                  refine ⟨2531294400001962804528833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1687529600001308536352555 2531294400001962804528833)
                  ·
                    refine ⟨1898470800001472103396625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2531294400001962804528833 1898470800001472103396625)
                    ·
                      refine ⟨1423853100001104077547469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1898470800001472103396625 1423853100001104077547469)
                      ·
                        rfl

theorem cell23_2772944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5, 1, 2, 2].length) (baseStart_2772944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772944 prefixEnd_2772944 := by exact prefixLift 2772944
  have htrace : WordTrace (prefixWord ++ tailWord_2772944) baseStart_2772944 baseEnd_2772944 := by
    simpa [prefixWord, tailWord_2772944, baseEnd_2772944] using wordTrace_append hprefix tailTrace_2772944
  have hstable : (prefixWord ++ tailWord_2772944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772944).length < 2 ^ (prefixWord ++ tailWord_2772944).sum := by decide
  have hdescent : baseEnd_2772944 < baseStart_2772944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772954 : List Nat := [3, 1, 1, 2, 5, 2, 1, 2, 2, 4]
def baseStart_2772954 : Nat := 118140960795 + 2772954 * 2 ^ 59
def prefixEnd_2772954 : Nat := 4983230072969 + 3 ^ 40 * 2772954 * 2
def baseEnd_2772954 : Nat := 474619411602549679474141

theorem tailTrace_2772954 : CollatzResearch.WordTrace tailWord_2772954 prefixEnd_2772954 474619411602549679474141 := by
  unfold tailWord_2772954
  simp only [CollatzResearch.WordTrace]
  refine ⟨25284485299017178921113479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67425294130712477122969277 25284485299017178921113479)
  ·
    refine ⟨37926727948525768381670219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25284485299017178921113479 37926727948525768381670219)
    ·
      refine ⟨56890091922788652572505329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37926727948525768381670219 56890091922788652572505329)
      ·
        refine ⟨42667568942091489429378997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56890091922788652572505329 42667568942091489429378997)
        ·
          refine ⟨4000084588321077134004281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42667568942091489429378997 4000084588321077134004281)
          ·
            refine ⟨3000063441240807850503211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4000084588321077134004281 3000063441240807850503211)
            ·
              refine ⟨4500095161861211775754817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3000063441240807850503211 4500095161861211775754817)
              ·
                refine ⟨3375071371395908831816113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4500095161861211775754817 3375071371395908831816113)
                ·
                  refine ⟨2531303528546931623862085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3375071371395908831816113 2531303528546931623862085)
                  ·
                    refine ⟨474619411602549679474141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2531303528546931623862085 474619411602549679474141)
                    ·
                      rfl

theorem cell23_2772954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 2, 4].length) (baseStart_2772954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772954 prefixEnd_2772954 := by exact prefixLift 2772954
  have htrace : WordTrace (prefixWord ++ tailWord_2772954) baseStart_2772954 baseEnd_2772954 := by
    simpa [prefixWord, tailWord_2772954, baseEnd_2772954] using wordTrace_append hprefix tailTrace_2772954
  have hstable : (prefixWord ++ tailWord_2772954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772954).length < 2 ^ (prefixWord ++ tailWord_2772954).sum := by decide
  have hdescent : baseEnd_2772954 < baseStart_2772954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772987 : List Nat := [1, 1, 1, 1, 1, 3, 5, 4, 1, 3, 2]
def baseStart_2772987 : Nat := 118140960795 + 2772987 * 2 ^ 59
def prefixEnd_2772987 : Nat := 4983230072969 + 3 ^ 40 * 2772987 * 2
def baseEnd_2772987 : Nat := 1423875179669247409309771

theorem tailTrace_2772987 : CollatzResearch.WordTrace tailWord_2772987 prefixEnd_2772987 1423875179669247409309771 := by
  unfold tailWord_2772987
  simp only [CollatzResearch.WordTrace]
  refine ⟨101139144804949162320405215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67426096536632774880270143 101139144804949162320405215)
  ·
    refine ⟨151708717207423743480607823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101139144804949162320405215 151708717207423743480607823)
    ·
      refine ⟨227563075811135615220911735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151708717207423743480607823 227563075811135615220911735)
      ·
        refine ⟨341344613716703422831367603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227563075811135615220911735 341344613716703422831367603)
        ·
          refine ⟨512016920575055134247051405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341344613716703422831367603 512016920575055134247051405)
          ·
            refine ⟨192006345215645675342644277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 512016920575055134247051405 192006345215645675342644277)
            ·
              refine ⟨18000594863966782063372901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 192006345215645675342644277 18000594863966782063372901)
              ·
                refine ⟨3375111536993771636882419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18000594863966782063372901 3375111536993771636882419)
                ·
                  refine ⟨5062667305490657455323629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3375111536993771636882419 5062667305490657455323629)
                  ·
                    refine ⟨1898500239558996545746361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5062667305490657455323629 1898500239558996545746361)
                    ·
                      refine ⟨1423875179669247409309771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1898500239558996545746361 1423875179669247409309771)
                      ·
                        rfl

theorem cell23_2772987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 3, 2].length) (baseStart_2772987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772987 prefixEnd_2772987 := by exact prefixLift 2772987
  have htrace : WordTrace (prefixWord ++ tailWord_2772987) baseStart_2772987 baseEnd_2772987 := by
    simpa [prefixWord, tailWord_2772987, baseEnd_2772987] using wordTrace_append hprefix tailTrace_2772987
  have hstable : (prefixWord ++ tailWord_2772987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772987).length < 2 ^ (prefixWord ++ tailWord_2772987).sum := by decide
  have hdescent : baseEnd_2772987 < baseStart_2772987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772998 : List Nat := [6, 2, 1, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_2772998 : Nat := 118140960795 + 2772998 * 2 ^ 59
def prefixEnd_2772998 : Nat := 4983230072969 + 3 ^ 40 * 2772998 * 2
def baseEnd_2772998 : Nat := 1423880827956446866272221

theorem tailTrace_2772998 : CollatzResearch.WordTrace tailWord_2772998 prefixEnd_2772998 1423880827956446866272221 := by
  unfold tailWord_2772998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3160610812747165974970489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67426364005272874132703765 3160610812747165974970489)
  ·
    refine ⟨2370458109560374481227867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3160610812747165974970489 2370458109560374481227867)
    ·
      refine ⟨3555687164340561721841801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2370458109560374481227867 3555687164340561721841801)
      ·
        refine ⟨2666765373255421291381351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3555687164340561721841801 2666765373255421291381351)
        ·
          refine ⟨4000148059883131937072027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2666765373255421291381351 4000148059883131937072027)
          ·
            refine ⟨6000222089824697905608041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4000148059883131937072027 6000222089824697905608041)
            ·
              refine ⟨4500166567368523429206031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6000222089824697905608041 4500166567368523429206031)
              ·
                refine ⟨6750249851052785143809047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4500166567368523429206031 6750249851052785143809047)
                ·
                  refine ⟨10125374776579177715713571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6750249851052785143809047 10125374776579177715713571)
                  ·
                    refine ⟨15188062164868766573570357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10125374776579177715713571 15188062164868766573570357)
                    ·
                      refine ⟨1423880827956446866272221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15188062164868766573570357 1423880827956446866272221)
                      ·
                        rfl

theorem cell23_2772998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_2772998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2772998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2772998 prefixEnd_2772998 := by exact prefixLift 2772998
  have htrace : WordTrace (prefixWord ++ tailWord_2772998) baseStart_2772998 baseEnd_2772998 := by
    simpa [prefixWord, tailWord_2772998, baseEnd_2772998] using wordTrace_append hprefix tailTrace_2772998
  have hstable : (prefixWord ++ tailWord_2772998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772998).length < 2 ^ (prefixWord ++ tailWord_2772998).sum := by decide
  have hdescent : baseEnd_2772998 < baseStart_2772998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773012 : List Nat := [2, 4, 3, 2, 1, 1, 3, 2, 1, 2, 2]
def baseStart_2773012 : Nat := 118140960795 + 2773012 * 2 ^ 59
def prefixEnd_2773012 : Nat := 4983230072969 + 3 ^ 40 * 2773012 * 2
def baseEnd_2773012 : Nat := 1423888016685609811497157

theorem tailTrace_2773012 : CollatzResearch.WordTrace tailWord_2773012 prefixEnd_2773012 1423888016685609811497157 := by
  unfold tailWord_2773012
  simp only [CollatzResearch.WordTrace]
  refine ⟨50570028314929295795032645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67426704419905727726710193 50570028314929295795032645)
  ·
    refine ⟨9481880309049242961568621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50570028314929295795032645 9481880309049242961568621)
    ·
      refine ⟨3555705115893466110588233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9481880309049242961568621 3555705115893466110588233)
      ·
        refine ⟨2666778836920099582941175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3555705115893466110588233 2666778836920099582941175)
        ·
          refine ⟨4000168255380149374411763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2666778836920099582941175 4000168255380149374411763)
          ·
            refine ⟨6000252383070224061617645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4000168255380149374411763 6000252383070224061617645)
            ·
              refine ⟨2250094643651334023106617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6000252383070224061617645 2250094643651334023106617)
              ·
                refine ⟨1687570982738500517329963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2250094643651334023106617 1687570982738500517329963)
                ·
                  refine ⟨2531356474107750775994945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1687570982738500517329963 2531356474107750775994945)
                  ·
                    refine ⟨1898517355580813081996209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2531356474107750775994945 1898517355580813081996209)
                    ·
                      refine ⟨1423888016685609811497157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1898517355580813081996209 1423888016685609811497157)
                      ·
                        rfl

theorem cell23_2773012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_2773012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773012 prefixEnd_2773012 := by exact prefixLift 2773012
  have htrace : WordTrace (prefixWord ++ tailWord_2773012) baseStart_2773012 baseEnd_2773012 := by
    simpa [prefixWord, tailWord_2773012, baseEnd_2773012] using wordTrace_append hprefix tailTrace_2773012
  have hstable : (prefixWord ++ tailWord_2773012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773012).length < 2 ^ (prefixWord ++ tailWord_2773012).sum := by decide
  have hdescent : baseEnd_2773012 < baseStart_2773012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773028 : List Nat := [2, 3, 1, 4, 2, 2, 2, 1, 2, 1, 3]
def baseStart_2773028 : Nat := 118140960795 + 2773028 * 2 ^ 59
def prefixEnd_2773028 : Nat := 4983230072969 + 3 ^ 40 * 2773028 * 2
def baseEnd_2773028 : Nat := 1423896232376081748897083

theorem tailTrace_2773028 : CollatzResearch.WordTrace tailWord_2773028 prefixEnd_2773028 1423896232376081748897083 := by
  unfold tailWord_2773028
  simp only [CollatzResearch.WordTrace]
  refine ⟨50570320098900313161323869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67427093465200417548431825 50570320098900313161323869)
  ·
    refine ⟨18963870037087617435496451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50570320098900313161323869 18963870037087617435496451)
    ·
      refine ⟨28445805055631426153244677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18963870037087617435496451 28445805055631426153244677)
      ·
        refine ⟨5333588447930892403733377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28445805055631426153244677 5333588447930892403733377)
        ·
          refine ⟨4000191335948169302800033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5333588447930892403733377 4000191335948169302800033)
          ·
            refine ⟨3000143501961126977100025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4000191335948169302800033 3000143501961126977100025)
            ·
              refine ⟨2250107626470845232825019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3000143501961126977100025 2250107626470845232825019)
              ·
                refine ⟨3375161439706267849237529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2250107626470845232825019 3375161439706267849237529)
                ·
                  refine ⟨2531371079779700886928147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3375161439706267849237529 2531371079779700886928147)
                  ·
                    refine ⟨3797056619669551330392221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2531371079779700886928147 3797056619669551330392221)
                    ·
                      refine ⟨1423896232376081748897083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3797056619669551330392221 1423896232376081748897083)
                      ·
                        rfl

theorem cell23_2773028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_2773028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773028 prefixEnd_2773028 := by exact prefixLift 2773028
  have htrace : WordTrace (prefixWord ++ tailWord_2773028) baseStart_2773028 baseEnd_2773028 := by
    simpa [prefixWord, tailWord_2773028, baseEnd_2773028] using wordTrace_append hprefix tailTrace_2773028
  have hstable : (prefixWord ++ tailWord_2773028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773028).length < 2 ^ (prefixWord ++ tailWord_2773028).sum := by decide
  have hdescent : baseEnd_2773028 < baseStart_2773028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773050 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3]
def baseStart_2773050 : Nat := 118140960795 + 2773050 * 2 ^ 59
def prefixEnd_2773050 : Nat := 4983230072969 + 3 ^ 40 * 2773050 * 2
def baseEnd_2773050 : Nat := 1423907528950480662821981

theorem tailTrace_2773050 : CollatzResearch.WordTrace tailWord_2773050 prefixEnd_2773050 1423907528950480662821981 := by
  unfold tailWord_2773050
  simp only [CollatzResearch.WordTrace]
  refine ⟨25285360650930231019987151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67427628402480616053299069 25285360650930231019987151)
  ·
    refine ⟨37928040976395346529980727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25285360650930231019987151 37928040976395346529980727)
    ·
      refine ⟨56892061464593019794971091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37928040976395346529980727 56892061464593019794971091)
      ·
        refine ⟨85338092196889529692456637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56892061464593019794971091 85338092196889529692456637)
        ·
          refine ⟨32001784573833573634671239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85338092196889529692456637 32001784573833573634671239)
          ·
            refine ⟨48002676860750360452006859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32001784573833573634671239 48002676860750360452006859)
            ·
              refine ⟨72004015291125540678010289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48002676860750360452006859 72004015291125540678010289)
              ·
                refine ⟨54003011468344155508507717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72004015291125540678010289 54003011468344155508507717)
                ·
                  refine ⟨10125564650314529157845197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54003011468344155508507717 10125564650314529157845197)
                  ·
                    refine ⟨3797086743867948434191949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10125564650314529157845197 3797086743867948434191949)
                    ·
                      refine ⟨1423907528950480662821981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3797086743867948434191949 1423907528950480662821981)
                      ·
                        rfl

theorem cell23_2773050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3].length) (baseStart_2773050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773050 prefixEnd_2773050 := by exact prefixLift 2773050
  have htrace : WordTrace (prefixWord ++ tailWord_2773050) baseStart_2773050 baseEnd_2773050 := by
    simpa [prefixWord, tailWord_2773050, baseEnd_2773050] using wordTrace_append hprefix tailTrace_2773050
  have hstable : (prefixWord ++ tailWord_2773050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773050).length < 2 ^ (prefixWord ++ tailWord_2773050).sum := by decide
  have hdescent : baseEnd_2773050 < baseStart_2773050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773074 : List Nat := [3, 2, 2, 1, 4, 1, 1, 4, 5]
def baseStart_2773074 : Nat := 118140960795 + 2773074 * 2 ^ 59
def prefixEnd_2773074 : Nat := 4983230072969 + 3 ^ 40 * 2773074 * 2
def baseEnd_2773074 : Nat := 158213316942909840991319

theorem tailTrace_2773074 : CollatzResearch.WordTrace tailWord_2773074 prefixEnd_2773074 158213316942909840991319 := by
  unfold tailWord_2773074
  simp only [CollatzResearch.WordTrace]
  refine ⟨25285579488908494044705569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67428211970422650785881517 25285579488908494044705569)
  ·
    refine ⟨18964184616681370533529177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25285579488908494044705569 18964184616681370533529177)
    ·
      refine ⟨14223138462511027900146883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18964184616681370533529177 14223138462511027900146883)
      ·
        refine ⟨21334707693766541850220325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14223138462511027900146883 21334707693766541850220325)
        ·
          refine ⟨4000257692581226596916311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21334707693766541850220325 4000257692581226596916311)
          ·
            refine ⟨6000386538871839895374467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4000257692581226596916311 6000386538871839895374467)
            ·
              refine ⟨9000579808307759843061701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6000386538871839895374467 9000579808307759843061701)
              ·
                refine ⟨1687608714057704970574069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9000579808307759843061701 1687608714057704970574069)
                ·
                  refine ⟨158213316942909840991319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1687608714057704970574069 158213316942909840991319)
                  ·
                    rfl

theorem cell23_2773074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4, 5].length) (baseStart_2773074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773074 prefixEnd_2773074 := by exact prefixLift 2773074
  have htrace : WordTrace (prefixWord ++ tailWord_2773074) baseStart_2773074 baseEnd_2773074 := by
    simpa [prefixWord, tailWord_2773074, baseEnd_2773074] using wordTrace_append hprefix tailTrace_2773074
  have hstable : (prefixWord ++ tailWord_2773074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773074).length < 2 ^ (prefixWord ++ tailWord_2773074).sum := by decide
  have hdescent : baseEnd_2773074 < baseStart_2773074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773077 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 2, 5, 2]
def baseStart_2773077 : Nat := 118140960795 + 2773077 * 2 ^ 59
def prefixEnd_2773077 : Nat := 4983230072969 + 3 ^ 40 * 2773077 * 2
def baseEnd_2773077 : Nat := 1423921392928152057184357

theorem tailTrace_2773077 : CollatzResearch.WordTrace tailWord_2773077 prefixEnd_2773077 1423921392928152057184357 := by
  unfold tailWord_2773077
  simp only [CollatzResearch.WordTrace]
  refine ⟨101142427374623107691181485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67428284916415405127454323 101142427374623107691181485)
  ·
    refine ⟨37928410265483665384193057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101142427374623107691181485 37928410265483665384193057)
    ·
      refine ⟨28446307699112749038144793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37928410265483665384193057 28446307699112749038144793)
      ·
        refine ⟨21334730774334561778608595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28446307699112749038144793 21334730774334561778608595)
        ·
          refine ⟨32002096161501842667912893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21334730774334561778608595 32002096161501842667912893)
          ·
            refine ⟨12000786060563191000467335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32002096161501842667912893 12000786060563191000467335)
            ·
              refine ⟨18001179090844786500701003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12000786060563191000467335 18001179090844786500701003)
              ·
                refine ⟨27001768636267179751051505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18001179090844786500701003 27001768636267179751051505)
                ·
                  refine ⟨20251326477200384813288629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27001768636267179751051505 20251326477200384813288629)
                  ·
                    refine ⟨1898561857237536076245809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20251326477200384813288629 1898561857237536076245809)
                    ·
                      refine ⟨1423921392928152057184357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1898561857237536076245809 1423921392928152057184357)
                      ·
                        rfl

theorem cell23_2773077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_2773077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773077 prefixEnd_2773077 := by exact prefixLift 2773077
  have htrace : WordTrace (prefixWord ++ tailWord_2773077) baseStart_2773077 baseEnd_2773077 := by
    simpa [prefixWord, tailWord_2773077, baseEnd_2773077] using wordTrace_append hprefix tailTrace_2773077
  have hstable : (prefixWord ++ tailWord_2773077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773077).length < 2 ^ (prefixWord ++ tailWord_2773077).sum := by decide
  have hdescent : baseEnd_2773077 < baseStart_2773077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773080 : List Nat := [2, 1, 2, 2, 1, 4, 2, 1, 1, 2, 5]
def baseStart_2773080 : Nat := 118140960795 + 2773080 * 2 ^ 59
def prefixEnd_2773080 : Nat := 4983230072969 + 3 ^ 40 * 2773080 * 2
def baseEnd_2773080 : Nat := 1423922933370115545446843

theorem tailTrace_2773080 : CollatzResearch.WordTrace tailWord_2773080 prefixEnd_2773080 1423922933370115545446843 := by
  unfold tailWord_2773080
  simp only [CollatzResearch.WordTrace]
  refine ⟨50571268396806119601770347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67428357862408159469027129 50571268396806119601770347)
  ·
    refine ⟨75856902595209179402655521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50571268396806119601770347 75856902595209179402655521)
    ·
      refine ⟨56892676946406884551991641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75856902595209179402655521 56892676946406884551991641)
      ·
        refine ⟨42669507709805163413993731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56892676946406884551991641 42669507709805163413993731)
        ·
          refine ⟨64004261564707745120990597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42669507709805163413993731 64004261564707745120990597)
          ·
            refine ⟨12000799043382702210185737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64004261564707745120990597 12000799043382702210185737)
            ·
              refine ⟨9000599282537026657639303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12000799043382702210185737 9000599282537026657639303)
              ·
                refine ⟨13500898923805539986458955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9000599282537026657639303 13500898923805539986458955)
                ·
                  refine ⟨20251348385708309979688433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13500898923805539986458955 20251348385708309979688433)
                  ·
                    refine ⟨15188511289281232484766325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20251348385708309979688433 15188511289281232484766325)
                    ·
                      refine ⟨1423922933370115545446843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15188511289281232484766325 1423922933370115545446843)
                      ·
                        rfl

theorem cell23_2773080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_2773080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773080 prefixEnd_2773080 := by exact prefixLift 2773080
  have htrace : WordTrace (prefixWord ++ tailWord_2773080) baseStart_2773080 baseEnd_2773080 := by
    simpa [prefixWord, tailWord_2773080, baseEnd_2773080] using wordTrace_append hprefix tailTrace_2773080
  have hstable : (prefixWord ++ tailWord_2773080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773080).length < 2 ^ (prefixWord ++ tailWord_2773080).sum := by decide
  have hdescent : baseEnd_2773080 < baseStart_2773080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773127 : List Nat := [1, 1, 4, 2, 1, 1, 2, 4, 2, 2, 3]
def baseStart_2773127 : Nat := 118140960795 + 2773127 * 2 ^ 59
def prefixEnd_2773127 : Nat := 4983230072969 + 3 ^ 40 * 2773127 * 2
def baseEnd_2773127 : Nat := 1423947066960876861559127

theorem tailTrace_2773127 : CollatzResearch.WordTrace tailWord_2773127 prefixEnd_2773127 1423947066960876861559127 := by
  unfold tailWord_2773127
  simp only [CollatzResearch.WordTrace]
  refine ⟨101144251024441966230501635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67429500682961310820334423 101144251024441966230501635)
  ·
    refine ⟨151716376536662949345752453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101144251024441966230501635 151716376536662949345752453)
    ·
      refine ⟨28446820600624303002328585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151716376536662949345752453 28446820600624303002328585)
      ·
        refine ⟨21335115450468227251746439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28446820600624303002328585 21335115450468227251746439)
        ·
          refine ⟨32002673175702340877619659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21335115450468227251746439 32002673175702340877619659)
          ·
            refine ⟨48004009763553511316429489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32002673175702340877619659 48004009763553511316429489)
            ·
              refine ⟨36003007322665133487322117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48004009763553511316429489 36003007322665133487322117)
              ·
                refine ⟨6750563872999712528872897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36003007322665133487322117 6750563872999712528872897)
                ·
                  refine ⟨5062922904749784396654673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6750563872999712528872897 5062922904749784396654673)
                  ·
                    refine ⟨3797192178562338297491005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5062922904749784396654673 3797192178562338297491005)
                    ·
                      refine ⟨1423947066960876861559127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3797192178562338297491005 1423947066960876861559127)
                      ·
                        rfl

theorem cell23_2773127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_2773127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773127 prefixEnd_2773127 := by exact prefixLift 2773127
  have htrace : WordTrace (prefixWord ++ tailWord_2773127) baseStart_2773127 baseEnd_2773127 := by
    simpa [prefixWord, tailWord_2773127, baseEnd_2773127] using wordTrace_append hprefix tailTrace_2773127
  have hstable : (prefixWord ++ tailWord_2773127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773127).length < 2 ^ (prefixWord ++ tailWord_2773127).sum := by decide
  have hdescent : baseEnd_2773127 < baseStart_2773127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773177 : List Nat := [1, 2, 1, 4, 1, 2, 1, 5, 1, 5]
def baseStart_2773177 : Nat := 118140960795 + 2773177 * 2 ^ 59
def prefixEnd_2773177 : Nat := 4983230072969 + 3 ^ 40 * 2773177 * 2
def baseEnd_2773177 : Nat := 474657580331200555311299

theorem tailTrace_2773177 : CollatzResearch.WordTrace tailWord_2773177 prefixEnd_2773177 474657580331200555311299 := by
  unfold tailWord_2773177
  simp only [CollatzResearch.WordTrace]
  refine ⟨101146074674260824769821785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67430716449507216513214523 101146074674260824769821785)
  ·
    refine ⟨75859556005695618577366339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101146074674260824769821785 75859556005695618577366339)
    ·
      refine ⟨113789334008543427866049509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75859556005695618577366339 113789334008543427866049509)
      ·
        refine ⟨21335500126601892724884283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113789334008543427866049509 21335500126601892724884283)
        ·
          refine ⟨32003250189902839087326425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21335500126601892724884283 32003250189902839087326425)
          ·
            refine ⟨24002437642427129315494819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32003250189902839087326425 24002437642427129315494819)
            ·
              refine ⟨36003656463640693973242229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24002437642427129315494819 36003656463640693973242229)
              ·
                refine ⟨3375342793466315059991459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36003656463640693973242229 3375342793466315059991459)
                ·
                  refine ⟨5063014190199472589987189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3375342793466315059991459 5063014190199472589987189)
                  ·
                    refine ⟨474657580331200555311299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5063014190199472589987189 474657580331200555311299)
                    ·
                      rfl

theorem cell23_2773177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 5].length) (baseStart_2773177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773177 prefixEnd_2773177 := by exact prefixLift 2773177
  have htrace : WordTrace (prefixWord ++ tailWord_2773177) baseStart_2773177 baseEnd_2773177 := by
    simpa [prefixWord, tailWord_2773177, baseEnd_2773177] using wordTrace_append hprefix tailTrace_2773177
  have hstable : (prefixWord ++ tailWord_2773177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773177).length < 2 ^ (prefixWord ++ tailWord_2773177).sum := by decide
  have hdescent : baseEnd_2773177 < baseStart_2773177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773184 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 4, 3, 2]
def baseStart_2773184 : Nat := 118140960795 + 2773184 * 2 ^ 59
def prefixEnd_2773184 : Nat := 4983230072969 + 3 ^ 40 * 2773184 * 2
def baseEnd_2773184 : Nat := 1423976335358183138546365

theorem tailTrace_2773184 : CollatzResearch.WordTrace tailWord_2773184 prefixEnd_2773184 1423976335358183138546365 := by
  unfold tailWord_2773184
  simp only [CollatzResearch.WordTrace]
  refine ⟨50573164992617732482663303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67430886656823643310217737 50573164992617732482663303)
  ·
    refine ⟨75859747488926598723994955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50573164992617732482663303 75859747488926598723994955)
    ·
      refine ⟨113789621233389898085992433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75859747488926598723994955 113789621233389898085992433)
      ·
        refine ⟨85342215925042423564494325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113789621233389898085992433 85342215925042423564494325)
        ·
          refine ⟨8000832742972727209171343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85342215925042423564494325 8000832742972727209171343)
          ·
            refine ⟨12001249114459090813757015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8000832742972727209171343 12001249114459090813757015)
            ·
              refine ⟨18001873671688636220635523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12001249114459090813757015 18001873671688636220635523)
              ·
                refine ⟨27002810507532954330953285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18001873671688636220635523 27002810507532954330953285)
                ·
                  refine ⟨5063026970162428937053741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27002810507532954330953285 5063026970162428937053741)
                  ·
                    refine ⟨1898635113810910851395153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5063026970162428937053741 1898635113810910851395153)
                    ·
                      refine ⟨1423976335358183138546365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1898635113810910851395153 1423976335358183138546365)
                      ·
                        rfl

theorem cell23_2773184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 4, 3, 2].length) (baseStart_2773184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773184 prefixEnd_2773184 := by exact prefixLift 2773184
  have htrace : WordTrace (prefixWord ++ tailWord_2773184) baseStart_2773184 baseEnd_2773184 := by
    simpa [prefixWord, tailWord_2773184, baseEnd_2773184] using wordTrace_append hprefix tailTrace_2773184
  have hstable : (prefixWord ++ tailWord_2773184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773184).length < 2 ^ (prefixWord ++ tailWord_2773184).sum := by decide
  have hdescent : baseEnd_2773184 < baseStart_2773184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773185 : List Nat := [1, 2, 6, 1, 2, 1, 3, 2, 1, 4]
def baseStart_2773185 : Nat := 118140960795 + 2773185 * 2 ^ 59
def prefixEnd_2773185 : Nat := 4983230072969 + 3 ^ 40 * 2773185 * 2
def baseEnd_2773185 : Nat := 474658949612945878211287

theorem tailTrace_2773185 : CollatzResearch.WordTrace tailWord_2773185 prefixEnd_2773185 474658949612945878211287 := by
  unfold tailWord_2773185
  simp only [CollatzResearch.WordTrace]
  refine ⟨101146366458231842136113009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67430910972154561424075339 101146366458231842136113009)
  ·
    refine ⟨75859774843673881602084757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101146366458231842136113009 75859774843673881602084757)
    ·
      refine ⟨3555926945797213200097723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 75859774843673881602084757 3555926945797213200097723)
      ·
        refine ⟨5333890418695819800146585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3555926945797213200097723 5333890418695819800146585)
        ·
          refine ⟨4000417814021864850109939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5333890418695819800146585 4000417814021864850109939)
          ·
            refine ⟨6000626721032797275164909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4000417814021864850109939 6000626721032797275164909)
            ·
              refine ⟨2250235020387298978186841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6000626721032797275164909 2250235020387298978186841)
              ·
                refine ⟨1687676265290474233640131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2250235020387298978186841 1687676265290474233640131)
                ·
                  refine ⟨2531514397935711350460197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1687676265290474233640131 2531514397935711350460197)
                  ·
                    refine ⟨474658949612945878211287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2531514397935711350460197 474658949612945878211287)
                    ·
                      rfl

theorem cell23_2773185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_2773185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773185 prefixEnd_2773185 := by exact prefixLift 2773185
  have htrace : WordTrace (prefixWord ++ tailWord_2773185) baseStart_2773185 baseEnd_2773185 := by
    simpa [prefixWord, tailWord_2773185, baseEnd_2773185] using wordTrace_append hprefix tailTrace_2773185
  have hstable : (prefixWord ++ tailWord_2773185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773185).length < 2 ^ (prefixWord ++ tailWord_2773185).sum := by decide
  have hdescent : baseEnd_2773185 < baseStart_2773185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773227 : List Nat := [1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 4]
def baseStart_2773227 : Nat := 118140960795 + 2773227 * 2 ^ 59
def prefixEnd_2773227 : Nat := 4983230072969 + 3 ^ 40 * 2773227 * 2
def baseEnd_2773227 : Nat := 1423998415026326470308667

theorem tailTrace_2773227 : CollatzResearch.WordTrace tailWord_2773227 prefixEnd_2773227 1423998415026326470308667 := by
  unfold tailWord_2773227
  simp only [CollatzResearch.WordTrace]
  refine ⟨101147898324079683309141935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67431932216053122206094623 101147898324079683309141935)
  ·
    refine ⟨151721847486119524963712903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101147898324079683309141935 151721847486119524963712903)
    ·
      refine ⟨227582771229179287445569355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151721847486119524963712903 227582771229179287445569355)
      ·
        refine ⟨341374156843768931168354033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227582771229179287445569355 341374156843768931168354033)
        ·
          refine ⟨256030617632826698376265525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341374156843768931168354033 256030617632826698376265525)
          ·
            refine ⟨24002870403077502972774893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 256030617632826698376265525 24002870403077502972774893)
            ·
              refine ⟨9001076401154063614790585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24002870403077502972774893 9001076401154063614790585)
              ·
                refine ⟨6750807300865547711092939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9001076401154063614790585 6750807300865547711092939)
                ·
                  refine ⟨10126210951298321566639409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6750807300865547711092939 10126210951298321566639409)
                  ·
                    refine ⟨7594658213473741174979557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10126210951298321566639409 7594658213473741174979557)
                    ·
                      refine ⟨1423998415026326470308667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7594658213473741174979557 1423998415026326470308667)
                      ·
                        rfl

theorem cell23_2773227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 4].length) (baseStart_2773227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773227 prefixEnd_2773227 := by exact prefixLift 2773227
  have htrace : WordTrace (prefixWord ++ tailWord_2773227) baseStart_2773227 baseEnd_2773227 := by
    simpa [prefixWord, tailWord_2773227, baseEnd_2773227] using wordTrace_append hprefix tailTrace_2773227
  have hstable : (prefixWord ++ tailWord_2773227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773227).length < 2 ^ (prefixWord ++ tailWord_2773227).sum := by decide
  have hdescent : baseEnd_2773227 < baseStart_2773227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773231 : List Nat := [1, 1, 2, 1, 6, 2, 3, 1, 1, 1, 4]
def baseStart_2773231 : Nat := 118140960795 + 2773231 * 2 ^ 59
def prefixEnd_2773231 : Nat := 4983230072969 + 3 ^ 40 * 2773231 * 2
def baseEnd_2773231 : Nat := 1424000468948944454658649

theorem tailTrace_2773231 : CollatzResearch.WordTrace tailWord_2773231 prefixEnd_2773231 1424000468948944454658649 := by
  unfold tailWord_2773231
  simp only [CollatzResearch.WordTrace]
  refine ⟨101148044216065191992287547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67432029477376794661525031 101148044216065191992287547)
  ·
    refine ⟨151722066324097787988431321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101148044216065191992287547 151722066324097787988431321)
    ·
      refine ⟨113791549743073340991323491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151722066324097787988431321 113791549743073340991323491)
      ·
        refine ⟨170687324614610011486985237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113791549743073340991323491 170687324614610011486985237)
        ·
          refine ⟨8000968341309844288452433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 170687324614610011486985237 8000968341309844288452433)
          ·
            refine ⟨6000726255982383216339325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8000968341309844288452433 6000726255982383216339325)
            ·
              refine ⟨2250272345993393706127247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6000726255982383216339325 2250272345993393706127247)
              ·
                refine ⟨3375408518990090559190871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2250272345993393706127247 3375408518990090559190871)
                ·
                  refine ⟨5063112778485135838786307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3375408518990090559190871 5063112778485135838786307)
                  ·
                    refine ⟨7594669167727703758179461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5063112778485135838786307 7594669167727703758179461)
                    ·
                      refine ⟨1424000468948944454658649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7594669167727703758179461 1424000468948944454658649)
                      ·
                        rfl

theorem cell23_2773231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 1, 1, 4].length) (baseStart_2773231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773231 prefixEnd_2773231 := by exact prefixLift 2773231
  have htrace : WordTrace (prefixWord ++ tailWord_2773231) baseStart_2773231 baseEnd_2773231 := by
    simpa [prefixWord, tailWord_2773231, baseEnd_2773231] using wordTrace_append hprefix tailTrace_2773231
  have hstable : (prefixWord ++ tailWord_2773231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773231).length < 2 ^ (prefixWord ++ tailWord_2773231).sum := by decide
  have hdescent : baseEnd_2773231 < baseStart_2773231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773234 : List Nat := [3, 2, 1, 3, 2, 1, 3, 1, 1, 1, 5]
def baseStart_2773234 : Nat := 118140960795 + 2773234 * 2 ^ 59
def prefixEnd_2773234 : Nat := 4983230072969 + 3 ^ 40 * 2773234 * 2
def baseEnd_2773234 : Nat := 1424002009390907942921135

theorem tailTrace_2773234 : CollatzResearch.WordTrace tailWord_2773234 prefixEnd_2773234 1424002009390907942921135 := by
  unfold tailWord_2773234
  simp only [CollatzResearch.WordTrace]
  refine ⟨25287038408763580876161689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67432102423369549003097837 25287038408763580876161689)
  ·
    refine ⟨18965278806572685657121267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25287038408763580876161689 18965278806572685657121267)
    ·
      refine ⟨28447918209859028485681901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18965278806572685657121267 28447918209859028485681901)
      ·
        refine ⟨10667969328697135682130713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28447918209859028485681901 10667969328697135682130713)
        ·
          refine ⟨8000976996522851761598035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10667969328697135682130713 8000976996522851761598035)
          ·
            refine ⟨12001465494784277642397053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8000976996522851761598035 12001465494784277642397053)
            ·
              refine ⟨4500549560544104115898895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12001465494784277642397053 4500549560544104115898895)
              ·
                refine ⟨6750824340816156173848343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4500549560544104115898895 6750824340816156173848343)
                ·
                  refine ⟨10126236511224234260772515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6750824340816156173848343 10126236511224234260772515)
                  ·
                    refine ⟨15189354766836351391158773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10126236511224234260772515 15189354766836351391158773)
                    ·
                      refine ⟨1424002009390907942921135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15189354766836351391158773 1424002009390907942921135)
                      ·
                        rfl

theorem cell23_2773234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_2773234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773234 prefixEnd_2773234 := by exact prefixLift 2773234
  have htrace : WordTrace (prefixWord ++ tailWord_2773234) baseStart_2773234 baseEnd_2773234 := by
    simpa [prefixWord, tailWord_2773234, baseEnd_2773234] using wordTrace_append hprefix tailTrace_2773234
  have hstable : (prefixWord ++ tailWord_2773234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773234).length < 2 ^ (prefixWord ++ tailWord_2773234).sum := by decide
  have hdescent : baseEnd_2773234 < baseStart_2773234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773247 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 3, 3, 3]
def baseStart_2773247 : Nat := 118140960795 + 2773247 * 2 ^ 59
def prefixEnd_2773247 : Nat := 4983230072969 + 3 ^ 40 * 2773247 * 2
def baseEnd_2773247 : Nat := 1424008684639416392058575

theorem tailTrace_2773247 : CollatzResearch.WordTrace tailWord_2773247 prefixEnd_2773247 1424008684639416392058575 := by
  unfold tailWord_2773247
  simp only [CollatzResearch.WordTrace]
  refine ⟨101148627784007226724869995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67432418522671484483246663 101148627784007226724869995)
  ·
    refine ⟨151722941676010840087304993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101148627784007226724869995 151722941676010840087304993)
    ·
      refine ⟨113792206257008130065478745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151722941676010840087304993 113792206257008130065478745)
      ·
        refine ⟨85344154692756097549109059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113792206257008130065478745 85344154692756097549109059)
        ·
          refine ⟨128016232039134146323663589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85344154692756097549109059 128016232039134146323663589)
          ·
            refine ⟨24003043507337652435686923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128016232039134146323663589 24003043507337652435686923)
            ·
              refine ⟨36004565261006478653530385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24003043507337652435686923 36004565261006478653530385)
              ·
                refine ⟨27003423945754858990147789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36004565261006478653530385 27003423945754858990147789)
                ·
                  refine ⟨10126283979658072121305421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27003423945754858990147789 10126283979658072121305421)
                  ·
                    refine ⟨3797356492371777045489533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10126283979658072121305421 3797356492371777045489533)
                    ·
                      refine ⟨1424008684639416392058575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3797356492371777045489533 1424008684639416392058575)
                      ·
                        rfl

theorem cell23_2773247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3, 3].length) (baseStart_2773247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773247 prefixEnd_2773247 := by exact prefixLift 2773247
  have htrace : WordTrace (prefixWord ++ tailWord_2773247) baseStart_2773247 baseEnd_2773247 := by
    simpa [prefixWord, tailWord_2773247, baseEnd_2773247] using wordTrace_append hprefix tailTrace_2773247
  have hstable : (prefixWord ++ tailWord_2773247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773247).length < 2 ^ (prefixWord ++ tailWord_2773247).sum := by decide
  have hdescent : baseEnd_2773247 < baseStart_2773247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773285 : List Nat := [1, 3, 1, 2, 6, 1, 2, 1, 1, 2, 3]
def baseStart_2773285 : Nat := 118140960795 + 2773285 * 2 ^ 59
def prefixEnd_2773285 : Nat := 4983230072969 + 3 ^ 40 * 2773285 * 2
def baseEnd_2773285 : Nat := 1424028196904287243383401

theorem tailTrace_2773285 : CollatzResearch.WordTrace tailWord_2773285 prefixEnd_2773285 1424028196904287243383401 := by
  unfold tailWord_2773285
  simp only [CollatzResearch.WordTrace]
  refine ⟨101150013757869559214753309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67433342505246372809835539 101150013757869559214753309)
  ·
    refine ⟨37931255159201084705532491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101150013757869559214753309 37931255159201084705532491)
    ·
      refine ⟨56896882738801627058298737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37931255159201084705532491 56896882738801627058298737)
      ·
        refine ⟨42672662054101220293724053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56896882738801627058298737 42672662054101220293724053)
        ·
          refine ⟨2000281033785994701268315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42672662054101220293724053 2000281033785994701268315)
          ·
            refine ⟨3000421550678992051902473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2000281033785994701268315 3000421550678992051902473)
            ·
              refine ⟨2250316163009244038926855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3000421550678992051902473 2250316163009244038926855)
              ·
                refine ⟨3375474244513866058390283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2250316163009244038926855 3375474244513866058390283)
                ·
                  refine ⟨5063211366770799087585425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3375474244513866058390283 5063211366770799087585425)
                  ·
                    refine ⟨3797408525078099315689069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5063211366770799087585425 3797408525078099315689069)
                    ·
                      refine ⟨1424028196904287243383401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3797408525078099315689069 1424028196904287243383401)
                      ·
                        rfl

theorem cell23_2773285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 1, 2, 3].length) (baseStart_2773285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773285 prefixEnd_2773285 := by exact prefixLift 2773285
  have htrace : WordTrace (prefixWord ++ tailWord_2773285) baseStart_2773285 baseEnd_2773285 := by
    simpa [prefixWord, tailWord_2773285, baseEnd_2773285] using wordTrace_append hprefix tailTrace_2773285
  have hstable : (prefixWord ++ tailWord_2773285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773285).length < 2 ^ (prefixWord ++ tailWord_2773285).sum := by decide
  have hdescent : baseEnd_2773285 < baseStart_2773285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773304 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 3, 4, 2]
def baseStart_2773304 : Nat := 118140960795 + 2773304 * 2 ^ 59
def prefixEnd_2773304 : Nat := 4983230072969 + 3 ^ 40 * 2773304 * 2
def baseEnd_2773304 : Nat := 1424037953036722669045813

theorem tailTrace_2773304 : CollatzResearch.WordTrace tailWord_2773304 prefixEnd_2773304 1424037953036722669045813 := by
  unfold tailWord_2773304
  simp only [CollatzResearch.WordTrace]
  refine ⟨50575353372400362729847483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67433804496533816973129977 50575353372400362729847483)
  ·
    refine ⟨75863030058600544094771225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50575353372400362729847483 75863030058600544094771225)
    ·
      refine ⟨56897272543950408071078419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75863030058600544094771225 56897272543950408071078419)
      ·
        refine ⟨85345908815925612106617629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56897272543950408071078419 85345908815925612106617629)
        ·
          refine ⟨32004715805972104539981611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85345908815925612106617629 32004715805972104539981611)
          ·
            refine ⟨48007073708958156809972417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32004715805972104539981611 48007073708958156809972417)
            ·
              refine ⟨36005305281718617607479313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48007073708958156809972417 36005305281718617607479313)
              ·
                refine ⟨27003978961288963205609485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36005305281718617607479313 27003978961288963205609485)
                ·
                  refine ⟨10126492110483361202103557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27003978961288963205609485 10126492110483361202103557)
                  ·
                    refine ⟨1898717270715630225394417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10126492110483361202103557 1898717270715630225394417)
                    ·
                      refine ⟨1424037953036722669045813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1898717270715630225394417 1424037953036722669045813)
                      ·
                        rfl

theorem cell23_2773304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 3, 4, 2].length) (baseStart_2773304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773304 prefixEnd_2773304 := by exact prefixLift 2773304
  have htrace : WordTrace (prefixWord ++ tailWord_2773304) baseStart_2773304 baseEnd_2773304 := by
    simpa [prefixWord, tailWord_2773304, baseEnd_2773304] using wordTrace_append hprefix tailTrace_2773304
  have hstable : (prefixWord ++ tailWord_2773304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773304).length < 2 ^ (prefixWord ++ tailWord_2773304).sum := by decide
  have hdescent : baseEnd_2773304 < baseStart_2773304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773417 : List Nat := [1, 2, 1, 1, 1, 1, 3, 5, 8]
def baseStart_2773417 : Nat := 118140960795 + 2773417 * 2 ^ 59
def prefixEnd_2773417 : Nat := 4983230072969 + 3 ^ 40 * 2773417 * 2
def baseEnd_2773417 : Nat := 158232886261186747436977

theorem tailTrace_2773417 : CollatzResearch.WordTrace tailWord_2773417 prefixEnd_2773417 158232886261186747436977 := by
  unfold tailWord_2773417
  simp only [CollatzResearch.WordTrace]
  refine ⟨101154828193391345758558505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67436552128927563839039003 101154828193391345758558505)
  ·
    refine ⟨75866121145043509318918879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101154828193391345758558505 75866121145043509318918879)
    ·
      refine ⟨113799181717565263978378319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75866121145043509318918879 113799181717565263978378319)
      ·
        refine ⟨170698772576347895967567479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113799181717565263978378319 170698772576347895967567479)
        ·
          refine ⟨256048158864521843951351219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170698772576347895967567479 256048158864521843951351219)
          ·
            refine ⟨384072238296782765927026829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256048158864521843951351219 384072238296782765927026829)
            ·
              refine ⟨144027089361293537222635061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 384072238296782765927026829 144027089361293537222635061)
              ·
                refine ⟨13502539627621269114622037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 144027089361293537222635061 13502539627621269114622037)
                ·
                  refine ⟨158232886261186747436977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13502539627621269114622037 158232886261186747436977)
                  ·
                    rfl

theorem cell23_2773417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 8].length) (baseStart_2773417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773417 prefixEnd_2773417 := by exact prefixLift 2773417
  have htrace : WordTrace (prefixWord ++ tailWord_2773417) baseStart_2773417 baseEnd_2773417 := by
    simpa [prefixWord, tailWord_2773417, baseEnd_2773417] using wordTrace_append hprefix tailTrace_2773417
  have hstable : (prefixWord ++ tailWord_2773417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773417).length < 2 ^ (prefixWord ++ tailWord_2773417).sum := by decide
  have hdescent : baseEnd_2773417 < baseStart_2773417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773448 : List Nat := [2, 1, 3, 1, 3, 4, 1, 1, 2, 2, 3]
def baseStart_2773448 : Nat := 118140960795 + 2773448 * 2 ^ 59
def prefixEnd_2773448 : Nat := 4983230072969 + 3 ^ 40 * 2773448 * 2
def baseEnd_2773448 : Nat := 1424111894250970105645151

theorem tailTrace_2773448 : CollatzResearch.WordTrace tailWord_2773448 prefixEnd_2773448 1424111894250970105645151 := by
  unfold tailWord_2773448
  simp only [CollatzResearch.WordTrace]
  refine ⟨50577979428139519026468499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67437305904186025368624665 50577979428139519026468499)
  ·
    refine ⟨75866969142209278539702749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50577979428139519026468499 75866969142209278539702749)
    ·
      refine ⟨28450113428328479452388531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75866969142209278539702749 28450113428328479452388531)
      ·
        refine ⟨42675170142492719178582797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28450113428328479452388531 42675170142492719178582797)
        ·
          refine ⟨16003188803434769691968549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42675170142492719178582797 16003188803434769691968549)
          ·
            refine ⟨3000597900644019317244103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16003188803434769691968549 3000597900644019317244103)
            ·
              refine ⟨4500896850966028975866155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3000597900644019317244103 4500896850966028975866155)
              ·
                refine ⟨6751345276449043463799233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4500896850966028975866155 6751345276449043463799233)
                ·
                  refine ⟨5063508957336782597849425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6751345276449043463799233 5063508957336782597849425)
                  ·
                    refine ⟨3797631718002586948387069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5063508957336782597849425 3797631718002586948387069)
                    ·
                      refine ⟨1424111894250970105645151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3797631718002586948387069 1424111894250970105645151)
                      ·
                        rfl

theorem cell23_2773448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_2773448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773448 prefixEnd_2773448 := by exact prefixLift 2773448
  have htrace : WordTrace (prefixWord ++ tailWord_2773448) baseStart_2773448 baseEnd_2773448 := by
    simpa [prefixWord, tailWord_2773448, baseEnd_2773448] using wordTrace_append hprefix tailTrace_2773448
  have hstable : (prefixWord ++ tailWord_2773448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773448).length < 2 ^ (prefixWord ++ tailWord_2773448).sum := by decide
  have hdescent : baseEnd_2773448 < baseStart_2773448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773501 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 2, 6, 2]
def baseStart_2773501 : Nat := 118140960795 + 2773501 * 2 ^ 59
def prefixEnd_2773501 : Nat := 4983230072969 + 3 ^ 40 * 2773501 * 2
def baseEnd_2773501 : Nat := 1424139108725658398282407

theorem tailTrace_2773501 : CollatzResearch.WordTrace tailWord_2773501 prefixEnd_2773501 1424139108725658398282407 := by
  unfold tailWord_2773501
  simp only [CollatzResearch.WordTrace]
  refine ⟨101157891925087028104616357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67438594616724685403077571 101157891925087028104616357)
  ·
    refine ⟨18967104735953817769615567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101157891925087028104616357 18967104735953817769615567)
    ·
      refine ⟨28450657103930726654423351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18967104735953817769615567 28450657103930726654423351)
      ·
        refine ⟨42675985655896089981635027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28450657103930726654423351 42675985655896089981635027)
        ·
          refine ⟨64013978483844134972452541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42675985655896089981635027 64013978483844134972452541)
          ·
            refine ⟨24005241931441550614669703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64013978483844134972452541 24005241931441550614669703)
            ·
              refine ⟨36007862897162325922004555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24005241931441550614669703 36007862897162325922004555)
              ·
                refine ⟨54011794345743488883006833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36007862897162325922004555 54011794345743488883006833)
                ·
                  refine ⟨40508845759307616662255125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54011794345743488883006833 40508845759307616662255125)
                  ·
                    refine ⟨1898852144967544531043209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40508845759307616662255125 1898852144967544531043209)
                    ·
                      refine ⟨1424139108725658398282407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1898852144967544531043209 1424139108725658398282407)
                      ·
                        rfl

theorem cell23_2773501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 6, 2].length) (baseStart_2773501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773501 prefixEnd_2773501 := by exact prefixLift 2773501
  have htrace : WordTrace (prefixWord ++ tailWord_2773501) baseStart_2773501 baseEnd_2773501 := by
    simpa [prefixWord, tailWord_2773501, baseEnd_2773501] using wordTrace_append hprefix tailTrace_2773501
  have hstable : (prefixWord ++ tailWord_2773501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773501).length < 2 ^ (prefixWord ++ tailWord_2773501).sum := by decide
  have hdescent : baseEnd_2773501 < baseStart_2773501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773504 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 3]
def baseStart_2773504 : Nat := 118140960795 + 2773504 * 2 ^ 59
def prefixEnd_2773504 : Nat := 4983230072969 + 3 ^ 40 * 2773504 * 2
def baseEnd_2773504 : Nat := 1424140649167621886544893

theorem tailTrace_2773504 : CollatzResearch.WordTrace tailWord_2773504 prefixEnd_2773504 1424140649167621886544893 := by
  unfold tailWord_2773504
  simp only [CollatzResearch.WordTrace]
  refine ⟨50579000672038079808487783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67438667562717439744650377 50579000672038079808487783)
  ·
    refine ⟨75868501008057119712731675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50579000672038079808487783 75868501008057119712731675)
    ·
      refine ⟨113802751512085679569097513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75868501008057119712731675 113802751512085679569097513)
      ·
        refine ⟨85352063634064259676823135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113802751512085679569097513 85352063634064259676823135)
        ·
          refine ⟨128028095451096389515234703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85352063634064259676823135 128028095451096389515234703)
          ·
            refine ⟨192042143176644584272852055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128028095451096389515234703 192042143176644584272852055)
            ·
              refine ⟨288063214764966876409278083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192042143176644584272852055 288063214764966876409278083)
              ·
                refine ⟨432094822147450314613917125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288063214764966876409278083 432094822147450314613917125)
                ·
                  refine ⟨81017779152646933990109461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 432094822147450314613917125 81017779152646933990109461)
                  ·
                    refine ⟨3797708397780325030786381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81017779152646933990109461 3797708397780325030786381)
                    ·
                      refine ⟨1424140649167621886544893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3797708397780325030786381 1424140649167621886544893)
                      ·
                        rfl

theorem cell23_2773504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 3].length) (baseStart_2773504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773504 prefixEnd_2773504 := by exact prefixLift 2773504
  have htrace : WordTrace (prefixWord ++ tailWord_2773504) baseStart_2773504 baseEnd_2773504 := by
    simpa [prefixWord, tailWord_2773504, baseEnd_2773504] using wordTrace_append hprefix tailTrace_2773504
  have hstable : (prefixWord ++ tailWord_2773504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773504).length < 2 ^ (prefixWord ++ tailWord_2773504).sum := by decide
  have hdescent : baseEnd_2773504 < baseStart_2773504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773518 : List Nat := [4, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4]
def baseStart_2773518 : Nat := 118140960795 + 2773518 * 2 ^ 59
def prefixEnd_2773518 : Nat := 4983230072969 + 3 ^ 40 * 2773518 * 2
def baseEnd_2773518 : Nat := 1424147837896784831769829

theorem tailTrace_2773518 : CollatzResearch.WordTrace tailWord_2773518 prefixEnd_2773518 1424147837896784831769829 := by
  unfold tailWord_2773518
  simp only [CollatzResearch.WordTrace]
  refine ⟨12644813995753180000998151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67439007977350293338656805 12644813995753180000998151)
  ·
    refine ⟨18967220993629770001497227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12644813995753180000998151 18967220993629770001497227)
    ·
      refine ⟨28450831490444655002245841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18967220993629770001497227 28450831490444655002245841)
      ·
        refine ⟨21338123617833491251684381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28450831490444655002245841 21338123617833491251684381)
        ·
          refine ⟨8001796356687559219381643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21338123617833491251684381 8001796356687559219381643)
          ·
            refine ⟨12002694535031338829072465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8001796356687559219381643 12002694535031338829072465)
            ·
              refine ⟨9002020901273504121804349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12002694535031338829072465 9002020901273504121804349)
              ·
                refine ⟨3375757837977564045676631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9002020901273504121804349 3375757837977564045676631)
                ·
                  refine ⟨5063636756966346068514947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3375757837977564045676631 5063636756966346068514947)
                  ·
                    refine ⟨7595455135449519102772421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5063636756966346068514947 7595455135449519102772421)
                    ·
                      refine ⟨1424147837896784831769829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7595455135449519102772421 1424147837896784831769829)
                      ·
                        rfl

theorem cell23_2773518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_2773518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773518 prefixEnd_2773518 := by exact prefixLift 2773518
  have htrace : WordTrace (prefixWord ++ tailWord_2773518) baseStart_2773518 baseEnd_2773518 := by
    simpa [prefixWord, tailWord_2773518, baseEnd_2773518] using wordTrace_append hprefix tailTrace_2773518
  have hstable : (prefixWord ++ tailWord_2773518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773518).length < 2 ^ (prefixWord ++ tailWord_2773518).sum := by decide
  have hdescent : baseEnd_2773518 < baseStart_2773518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773549 : List Nat := [1, 5, 4, 1, 1, 2, 1, 2, 1, 5]
def baseStart_2773549 : Nat := 118140960795 + 2773549 * 2 ^ 59
def prefixEnd_2773549 : Nat := 4983230072969 + 3 ^ 40 * 2773549 * 2
def baseEnd_2773549 : Nat := 474721251932358070160729

theorem tailTrace_2773549 : CollatzResearch.WordTrace tailWord_2773549 prefixEnd_2773549 474721251932358070160729 := by
  unfold tailWord_2773549
  simp only [CollatzResearch.WordTrace]
  refine ⟨101159642628913132302363701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67439761752608754868242467 101159642628913132302363701)
  ·
    refine ⟨9483716496460606153346597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101159642628913132302363701 9483716496460606153346597)
    ·
      refine ⟨1778196843086363653752487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9483716496460606153346597 1778196843086363653752487)
      ·
        refine ⟨2667295264629545480628731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1778196843086363653752487 2667295264629545480628731)
        ·
          refine ⟨4000942896944318220943097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2667295264629545480628731 4000942896944318220943097)
          ·
            refine ⟨3000707172708238665707323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4000942896944318220943097 3000707172708238665707323)
            ·
              refine ⟨4501060759062357998560985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3000707172708238665707323 4501060759062357998560985)
              ·
                refine ⟨3375795569296768498920739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4501060759062357998560985 3375795569296768498920739)
                ·
                  refine ⟨5063693353945152748381109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3375795569296768498920739 5063693353945152748381109)
                  ·
                    refine ⟨474721251932358070160729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5063693353945152748381109 474721251932358070160729)
                    ·
                      rfl

theorem cell23_2773549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_2773549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773549 prefixEnd_2773549 := by exact prefixLift 2773549
  have htrace : WordTrace (prefixWord ++ tailWord_2773549) baseStart_2773549 baseEnd_2773549 := by
    simpa [prefixWord, tailWord_2773549, baseEnd_2773549] using wordTrace_append hprefix tailTrace_2773549
  have hstable : (prefixWord ++ tailWord_2773549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773549).length < 2 ^ (prefixWord ++ tailWord_2773549).sum := by decide
  have hdescent : baseEnd_2773549 < baseStart_2773549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773585 : List Nat := [1, 2, 2, 1, 3, 4, 2, 2, 2, 1, 3]
def baseStart_2773585 : Nat := 118140960795 + 2773585 * 2 ^ 59
def prefixEnd_2773585 : Nat := 4983230072969 + 3 ^ 40 * 2773585 * 2
def baseEnd_2773585 : Nat := 1424182241100636069632021

theorem tailTrace_2773585 : CollatzResearch.WordTrace tailWord_2773585 prefixEnd_2773585 1424182241100636069632021 := by
  unfold tailWord_2773585
  simp only [CollatzResearch.WordTrace]
  refine ⟨101160955656782710450674209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67440637104521806967116139 101160955656782710450674209)
  ·
    refine ⟨75870716742587032838005657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101160955656782710450674209 75870716742587032838005657)
    ·
      refine ⟨56903037556940274628504243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75870716742587032838005657 56903037556940274628504243)
      ·
        refine ⟨85354556335410411942756365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56903037556940274628504243 85354556335410411942756365)
        ·
          refine ⟨32007958625778904478533637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85354556335410411942756365 32007958625778904478533637)
          ·
            refine ⟨6001492242333544589725057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32007958625778904478533637 6001492242333544589725057)
            ·
              refine ⟨4501119181750158442293793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6001492242333544589725057 4501119181750158442293793)
              ·
                refine ⟨3375839386312618831720345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4501119181750158442293793 3375839386312618831720345)
                ·
                  refine ⟨2531879539734464123790259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3375839386312618831720345 2531879539734464123790259)
                  ·
                    refine ⟨3797819309601696185685389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2531879539734464123790259 3797819309601696185685389)
                    ·
                      refine ⟨1424182241100636069632021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3797819309601696185685389 1424182241100636069632021)
                      ·
                        rfl

theorem cell23_2773585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2, 1, 3].length) (baseStart_2773585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773585 prefixEnd_2773585 := by exact prefixLift 2773585
  have htrace : WordTrace (prefixWord ++ tailWord_2773585) baseStart_2773585 baseEnd_2773585 := by
    simpa [prefixWord, tailWord_2773585, baseEnd_2773585] using wordTrace_append hprefix tailTrace_2773585
  have hstable : (prefixWord ++ tailWord_2773585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773585).length < 2 ^ (prefixWord ++ tailWord_2773585).sum := by decide
  have hdescent : baseEnd_2773585 < baseStart_2773585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773601 : List Nat := [1, 2, 3, 1, 1, 5, 1, 1, 2, 6]
def baseStart_2773601 : Nat := 118140960795 + 2773601 * 2 ^ 59
def prefixEnd_2773601 : Nat := 4983230072969 + 3 ^ 40 * 2773601 * 2
def baseEnd_2773601 : Nat := 474730152263702669010649

theorem tailTrace_2773601 : CollatzResearch.WordTrace tailWord_2773601 prefixEnd_2773601 474730152263702669010649 := by
  unfold tailWord_2773601
  simp only [CollatzResearch.WordTrace]
  refine ⟨101161539224724745183256657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67441026149816496788837771 101161539224724745183256657)
  ·
    refine ⟨75871154418543558887442493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101161539224724745183256657 75871154418543558887442493)
    ·
      refine ⟨28451682906953834582790935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75871154418543558887442493 28451682906953834582790935)
      ·
        refine ⟨42677524360430751874186403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28451682906953834582790935 42677524360430751874186403)
        ·
          refine ⟨64016286540646127811279605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42677524360430751874186403 64016286540646127811279605)
          ·
            refine ⟨6001526863185574482307463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64016286540646127811279605 6001526863185574482307463)
            ·
              refine ⟨9002290294778361723461195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6001526863185574482307463 9002290294778361723461195)
              ·
                refine ⟨13503435442167542585191793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9002290294778361723461195 13503435442167542585191793)
                ·
                  refine ⟨10127576581625656938893845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13503435442167542585191793 10127576581625656938893845)
                  ·
                    refine ⟨474730152263702669010649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10127576581625656938893845 474730152263702669010649)
                    ·
                      rfl

theorem cell23_2773601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_2773601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773601 prefixEnd_2773601 := by exact prefixLift 2773601
  have htrace : WordTrace (prefixWord ++ tailWord_2773601) baseStart_2773601 baseEnd_2773601 := by
    simpa [prefixWord, tailWord_2773601, baseEnd_2773601] using wordTrace_append hprefix tailTrace_2773601
  have hstable : (prefixWord ++ tailWord_2773601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773601).length < 2 ^ (prefixWord ++ tailWord_2773601).sum := by decide
  have hdescent : baseEnd_2773601 < baseStart_2773601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773602 : List Nat := [3, 3, 2, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_2773602 : Nat := 118140960795 + 2773602 * 2 ^ 59
def prefixEnd_2773602 : Nat := 4983230072969 + 3 ^ 40 * 2773602 * 2
def baseEnd_2773602 : Nat := 1424190970271762503119443

theorem tailTrace_2773602 : CollatzResearch.WordTrace tailWord_2773602 prefixEnd_2773602 1424190970271762503119443 := by
  unfold tailWord_2773602
  simp only [CollatzResearch.WordTrace]
  refine ⟨25290393924430280588510765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67441050465147414902695373 25290393924430280588510765)
  ·
    refine ⟨9483897721661355220691537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25290393924430280588510765 9483897721661355220691537)
    ·
      refine ⟨7112923291246016415518653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9483897721661355220691537 7112923291246016415518653)
      ·
        refine ⟨2667346234217256155819495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7112923291246016415518653 2667346234217256155819495)
        ·
          refine ⟨4001019351325884233729243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2667346234217256155819495 4001019351325884233729243)
          ·
            refine ⟨6001529026988826350593865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4001019351325884233729243 6001529026988826350593865)
            ·
              refine ⟨4501146770241619762945399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6001529026988826350593865 4501146770241619762945399)
              ·
                refine ⟨6751720155362429644418099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4501146770241619762945399 6751720155362429644418099)
                ·
                  refine ⟨10127580233043644466627149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6751720155362429644418099 10127580233043644466627149)
                  ·
                    refine ⟨3797842587391366674985181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10127580233043644466627149 3797842587391366674985181)
                    ·
                      refine ⟨1424190970271762503119443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3797842587391366674985181 1424190970271762503119443)
                      ·
                        rfl

theorem cell23_2773602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_2773602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773602 prefixEnd_2773602 := by exact prefixLift 2773602
  have htrace : WordTrace (prefixWord ++ tailWord_2773602) baseStart_2773602 baseEnd_2773602 := by
    simpa [prefixWord, tailWord_2773602, baseEnd_2773602] using wordTrace_append hprefix tailTrace_2773602
  have hstable : (prefixWord ++ tailWord_2773602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773602).length < 2 ^ (prefixWord ++ tailWord_2773602).sum := by decide
  have hdescent : baseEnd_2773602 < baseStart_2773602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773629 : List Nat := [1, 4, 1, 1, 5, 2, 2, 1, 1, 3, 2]
def baseStart_2773629 : Nat := 118140960795 + 2773629 * 2 ^ 59
def prefixEnd_2773629 : Nat := 4983230072969 + 3 ^ 40 * 2773629 * 2
def baseEnd_2773629 : Nat := 1424204834249433897481819

theorem tailTrace_2773629 : CollatzResearch.WordTrace tailWord_2773629 prefixEnd_2773629 1424204834249433897481819 := by
  unfold tailWord_2773629
  simp only [CollatzResearch.WordTrace]
  refine ⟨101162560468623305965275941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67441706979082203976850627 101162560468623305965275941)
  ·
    refine ⟨18967980087866869868489239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101162560468623305965275941 18967980087866869868489239)
    ·
      refine ⟨28451970131800304802733859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18967980087866869868489239 28451970131800304802733859)
      ·
        refine ⟨42677955197700457204100789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28451970131800304802733859 42677955197700457204100789)
        ·
          refine ⟨4001058299784417862884449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42677955197700457204100789 4001058299784417862884449)
          ·
            refine ⟨3000793724838313397163337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4001058299784417862884449 3000793724838313397163337)
            ·
              refine ⟨2250595293628735047872503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3000793724838313397163337 2250595293628735047872503)
              ·
                refine ⟨3375892940443102571808755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2250595293628735047872503 3375892940443102571808755)
                ·
                  refine ⟨5063839410664653857713133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3375892940443102571808755 5063839410664653857713133)
                  ·
                    refine ⟨1898939778999245196642425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5063839410664653857713133 1898939778999245196642425)
                    ·
                      refine ⟨1424204834249433897481819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1898939778999245196642425 1424204834249433897481819)
                      ·
                        rfl

theorem cell23_2773629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 1, 3, 2].length) (baseStart_2773629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773629 prefixEnd_2773629 := by exact prefixLift 2773629
  have htrace : WordTrace (prefixWord ++ tailWord_2773629) baseStart_2773629 baseEnd_2773629 := by
    simpa [prefixWord, tailWord_2773629, baseEnd_2773629] using wordTrace_append hprefix tailTrace_2773629
  have hstable : (prefixWord ++ tailWord_2773629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773629).length < 2 ^ (prefixWord ++ tailWord_2773629).sum := by decide
  have hdescent : baseEnd_2773629 < baseStart_2773629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773642 : List Nat := [3, 1, 2, 3, 3, 1, 1, 1, 4, 2, 2]
def baseStart_2773642 : Nat := 118140960795 + 2773642 * 2 ^ 59
def prefixEnd_2773642 : Nat := 4983230072969 + 3 ^ 40 * 2773642 * 2
def baseEnd_2773642 : Nat := 1424211509497942346619259

theorem tailTrace_2773642 : CollatzResearch.WordTrace tailWord_2773642 prefixEnd_2773642 1424211509497942346619259 := by
  unfold tailWord_2773642
  simp only [CollatzResearch.WordTrace]
  refine ⟨25290758654394052296374795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67442023078384139456999453 25290758654394052296374795)
  ·
    refine ⟨37936137981591078444562193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25290758654394052296374795 37936137981591078444562193)
    ·
      refine ⟨28452103486193308833421645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37936137981591078444562193 28452103486193308833421645)
      ·
        refine ⟨10669538807322490812533117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28452103486193308833421645 10669538807322490812533117)
        ·
          refine ⟨4001077052745934054699919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10669538807322490812533117 4001077052745934054699919)
          ·
            refine ⟨6001615579118901082049879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4001077052745934054699919 6001615579118901082049879)
            ·
              refine ⟨9002423368678351623074819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6001615579118901082049879 9002423368678351623074819)
              ·
                refine ⟨13503635053017527434612229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9002423368678351623074819 13503635053017527434612229)
                ·
                  refine ⟨2531931572440786393989793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13503635053017527434612229 2531931572440786393989793)
                  ·
                    refine ⟨1898948679330589795492345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2531931572440786393989793 1898948679330589795492345)
                    ·
                      refine ⟨1424211509497942346619259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1898948679330589795492345 1424211509497942346619259)
                      ·
                        rfl

theorem cell23_2773642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_2773642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773642 prefixEnd_2773642 := by exact prefixLift 2773642
  have htrace : WordTrace (prefixWord ++ tailWord_2773642) baseStart_2773642 baseEnd_2773642 := by
    simpa [prefixWord, tailWord_2773642, baseEnd_2773642] using wordTrace_append hprefix tailTrace_2773642
  have hstable : (prefixWord ++ tailWord_2773642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773642).length < 2 ^ (prefixWord ++ tailWord_2773642).sum := by decide
  have hdescent : baseEnd_2773642 < baseStart_2773642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773661 : List Nat := [1, 4, 2, 1, 1, 1, 3, 2, 1, 7]
def baseStart_2773661 : Nat := 118140960795 + 2773661 * 2 ^ 59
def prefixEnd_2773661 : Nat := 4983230072969 + 3 ^ 40 * 2773661 * 2
def baseEnd_2773661 : Nat := 474740421876792590760557

theorem tailTrace_2773661 : CollatzResearch.WordTrace tailWord_2773661 prefixEnd_2773661 474740421876792590760557 := by
  unfold tailWord_2773661
  simp only [CollatzResearch.WordTrace]
  refine ⟨101163727604507375430440837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67442485069671583620293891 101163727604507375430440837)
  ·
    refine ⟨18968198925845132893207657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101163727604507375430440837 18968198925845132893207657)
    ·
      refine ⟨14226149194383849669905743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18968198925845132893207657 14226149194383849669905743)
      ·
        refine ⟨21339223791575774504858615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14226149194383849669905743 21339223791575774504858615)
        ·
          refine ⟨32008835687363661757287923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21339223791575774504858615 32008835687363661757287923)
          ·
            refine ⟨48013253531045492635931885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32008835687363661757287923 48013253531045492635931885)
            ·
              refine ⟨18004970074142059738474457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48013253531045492635931885 18004970074142059738474457)
              ·
                refine ⟨13503727555606544803855843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18004970074142059738474457 13503727555606544803855843)
                ·
                  refine ⟨20255591333409817205783765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13503727555606544803855843 20255591333409817205783765)
                  ·
                    refine ⟨474740421876792590760557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20255591333409817205783765 474740421876792590760557)
                    ·
                      rfl

theorem cell23_2773661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_2773661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773661 prefixEnd_2773661 := by exact prefixLift 2773661
  have htrace : WordTrace (prefixWord ++ tailWord_2773661) baseStart_2773661 baseEnd_2773661 := by
    simpa [prefixWord, tailWord_2773661, baseEnd_2773661] using wordTrace_append hprefix tailTrace_2773661
  have hstable : (prefixWord ++ tailWord_2773661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773661).length < 2 ^ (prefixWord ++ tailWord_2773661).sum := by decide
  have hdescent : baseEnd_2773661 < baseStart_2773661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773768 : List Nat := [2, 1, 3, 2, 2, 2, 1, 2, 3, 5]
def baseStart_2773768 : Nat := 118140960795 + 2773768 * 2 ^ 59
def prefixEnd_2773768 : Nat := 4983230072969 + 3 ^ 40 * 2773768 * 2
def baseEnd_2773768 : Nat := 474758736020136284547893

theorem tailTrace_2773768 : CollatzResearch.WordTrace tailWord_2773768 prefixEnd_2773768 474758736020136284547893 := by
  unfold tailWord_2773768
  simp only [CollatzResearch.WordTrace]
  refine ⟨50583815107559866352292979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67445086810079821803057305 50583815107559866352292979)
  ·
    refine ⟨75875722661339799528439469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50583815107559866352292979 75875722661339799528439469)
    ·
      refine ⟨28453395998002424823164801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75875722661339799528439469 28453395998002424823164801)
      ·
        refine ⟨21340046998501818617373601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28453395998002424823164801 21340046998501818617373601)
        ·
          refine ⟨16005035248876363963030201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21340046998501818617373601 16005035248876363963030201)
          ·
            refine ⟨12003776436657272972272651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16005035248876363963030201 12003776436657272972272651)
            ·
              refine ⟨18005664654985909458408977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12003776436657272972272651 18005664654985909458408977)
              ·
                refine ⟨13504248491239432093806733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18005664654985909458408977 13504248491239432093806733)
                ·
                  refine ⟨5064093184214787035177525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13504248491239432093806733 5064093184214787035177525)
                  ·
                    refine ⟨474758736020136284547893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5064093184214787035177525 474758736020136284547893)
                    ·
                      rfl

theorem cell23_2773768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_2773768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773768 prefixEnd_2773768 := by exact prefixLift 2773768
  have htrace : WordTrace (prefixWord ++ tailWord_2773768) baseStart_2773768 baseEnd_2773768 := by
    simpa [prefixWord, tailWord_2773768, baseEnd_2773768] using wordTrace_append hprefix tailTrace_2773768
  have hstable : (prefixWord ++ tailWord_2773768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773768).length < 2 ^ (prefixWord ++ tailWord_2773768).sum := by decide
  have hdescent : baseEnd_2773768 < baseStart_2773768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773792 : List Nat := [2, 1, 1, 5, 1, 2, 3, 1, 2, 3, 2]
def baseStart_2773792 : Nat := 118140960795 + 2773792 * 2 ^ 59
def prefixEnd_2773792 : Nat := 4983230072969 + 3 ^ 40 * 2773792 * 2
def baseEnd_2773792 : Nat := 1424288531596116759743569

theorem tailTrace_2773792 : CollatzResearch.WordTrace tailWord_2773792 prefixEnd_2773792 1424288531596116759743569 := by
  unfold tailWord_2773792
  simp only [CollatzResearch.WordTrace]
  refine ⟨50584252783516392401729815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67445670378021856535639753 50584252783516392401729815)
  ·
    refine ⟨75876379175274588602594723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50584252783516392401729815 75876379175274588602594723)
    ·
      refine ⟨113814568762911882903892085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75876379175274588602594723 113814568762911882903892085)
      ·
        refine ⟨10670115821522989022239883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113814568762911882903892085 10670115821522989022239883)
        ·
          refine ⟨16005173732284483533359825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10670115821522989022239883 16005173732284483533359825)
          ·
            refine ⟨12003880299213362650019869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16005173732284483533359825 12003880299213362650019869)
            ·
              refine ⟨4501455112205010993757451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12003880299213362650019869 4501455112205010993757451)
              ·
                refine ⟨6752182668307516490636177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4501455112205010993757451 6752182668307516490636177)
                ·
                  refine ⟨5064137001230637367977133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6752182668307516490636177 5064137001230637367977133)
                  ·
                    refine ⟨1899051375461489012991425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5064137001230637367977133 1899051375461489012991425)
                    ·
                      refine ⟨1424288531596116759743569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1899051375461489012991425 1424288531596116759743569)
                      ·
                        rfl

theorem cell23_2773792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_2773792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773792 prefixEnd_2773792 := by exact prefixLift 2773792
  have htrace : WordTrace (prefixWord ++ tailWord_2773792) baseStart_2773792 baseEnd_2773792 := by
    simpa [prefixWord, tailWord_2773792, baseEnd_2773792] using wordTrace_append hprefix tailTrace_2773792
  have hstable : (prefixWord ++ tailWord_2773792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773792).length < 2 ^ (prefixWord ++ tailWord_2773792).sum := by decide
  have hdescent : baseEnd_2773792 < baseStart_2773792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773832 : List Nat := [2, 1, 3, 1, 1, 3, 5, 1, 2, 4]
def baseStart_2773832 : Nat := 118140960795 + 2773832 * 2 ^ 59
def prefixEnd_2773832 : Nat := 4983230072969 + 3 ^ 40 * 2773832 * 2
def baseEnd_2773832 : Nat := 474769690274098867747795

theorem tailTrace_2773832 : CollatzResearch.WordTrace tailWord_2773832 prefixEnd_2773832 474769690274098867747795 := by
  unfold tailWord_2773832
  simp only [CollatzResearch.WordTrace]
  refine ⟨50584982243443935817457875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67446642991258581089943833 50584982243443935817457875)
  ·
    refine ⟨75877473365165903726186813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50584982243443935817457875 75877473365165903726186813)
    ·
      refine ⟨28454052511937213897320055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75877473365165903726186813 28454052511937213897320055)
      ·
        refine ⟨42681078767905820845980083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28454052511937213897320055 42681078767905820845980083)
        ·
          refine ⟨64021618151858731268970125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42681078767905820845980083 64021618151858731268970125)
          ·
            refine ⟨24008106806947024225863797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64021618151858731268970125 24008106806947024225863797)
            ·
              refine ⟨2250760013151283521174731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24008106806947024225863797 2250760013151283521174731)
              ·
                refine ⟨3376140019726925281762097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2250760013151283521174731 3376140019726925281762097)
                ·
                  refine ⟨2532105014795193961321573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3376140019726925281762097 2532105014795193961321573)
                  ·
                    refine ⟨474769690274098867747795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2532105014795193961321573 474769690274098867747795)
                    ·
                      rfl

theorem cell23_2773832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_2773832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773832 prefixEnd_2773832 := by exact prefixLift 2773832
  have htrace : WordTrace (prefixWord ++ tailWord_2773832) baseStart_2773832 baseEnd_2773832 := by
    simpa [prefixWord, tailWord_2773832, baseEnd_2773832] using wordTrace_append hprefix tailTrace_2773832
  have hstable : (prefixWord ++ tailWord_2773832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773832).length < 2 ^ (prefixWord ++ tailWord_2773832).sum := by decide
  have hdescent : baseEnd_2773832 < baseStart_2773832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773842 : List Nat := [3, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3]
def baseStart_2773842 : Nat := 118140960795 + 2773842 * 2 ^ 59
def prefixEnd_2773842 : Nat := 4983230072969 + 3 ^ 40 * 2773842 * 2
def baseEnd_2773842 : Nat := 1424314205628841564118339

theorem tailTrace_2773842 : CollatzResearch.WordTrace tailWord_2773842 prefixEnd_2773842 1424314205628841564118339 := by
  unfold tailWord_2773842
  simp only [CollatzResearch.WordTrace]
  refine ⟨25292582304212910835694945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67446886144567762228519853 25292582304212910835694945)
  ·
    refine ⟨18969436728159683126771209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25292582304212910835694945 18969436728159683126771209)
    ·
      refine ⟨14227077546119762345078407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18969436728159683126771209 14227077546119762345078407)
      ·
        refine ⟨21340616319179643517617611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14227077546119762345078407 21340616319179643517617611)
        ·
          refine ⟨32010924478769465276426417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21340616319179643517617611 32010924478769465276426417)
          ·
            refine ⟨24008193359077098957319813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32010924478769465276426417 24008193359077098957319813)
            ·
              refine ⟨4501536254826956054497465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24008193359077098957319813 4501536254826956054497465)
              ·
                refine ⟨3376152191120217040873099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4501536254826956054497465 3376152191120217040873099)
                ·
                  refine ⟨5064228286680325561309649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3376152191120217040873099 5064228286680325561309649)
                  ·
                    refine ⟨3798171215010244170982237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5064228286680325561309649 3798171215010244170982237)
                    ·
                      refine ⟨1424314205628841564118339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3798171215010244170982237 1424314205628841564118339)
                      ·
                        rfl

theorem cell23_2773842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_2773842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773842 prefixEnd_2773842 := by exact prefixLift 2773842
  have htrace : WordTrace (prefixWord ++ tailWord_2773842) baseStart_2773842 baseEnd_2773842 := by
    simpa [prefixWord, tailWord_2773842, baseEnd_2773842] using wordTrace_append hprefix tailTrace_2773842
  have hstable : (prefixWord ++ tailWord_2773842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773842).length < 2 ^ (prefixWord ++ tailWord_2773842).sum := by decide
  have hdescent : baseEnd_2773842 < baseStart_2773842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773855 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 6, 1, 3]
def baseStart_2773855 : Nat := 118140960795 + 2773855 * 2 ^ 59
def prefixEnd_2773855 : Nat := 4983230072969 + 3 ^ 40 * 2773855 * 2
def baseEnd_2773855 : Nat := 1424320880877350013255779

theorem tailTrace_2773855 : CollatzResearch.WordTrace tailWord_2773855 prefixEnd_2773855 1424320880877350013255779 := by
  unfold tailWord_2773855
  simp only [CollatzResearch.WordTrace]
  refine ⟨101170803365804546563003019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67447202243869697708668679 101170803365804546563003019)
  ·
    refine ⟨151756205048706819844504529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101170803365804546563003019 151756205048706819844504529)
    ·
      refine ⟨113817153786530114883378397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151756205048706819844504529 113817153786530114883378397)
      ·
        refine ⟨42681432669948793081266899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113817153786530114883378397 42681432669948793081266899)
        ·
          refine ⟨64022149004923189621900349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42681432669948793081266899 64022149004923189621900349)
          ·
            refine ⟨24008305876846196108212631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64022149004923189621900349 24008305876846196108212631)
            ·
              refine ⟨36012458815269294162318947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24008305876846196108212631 36012458815269294162318947)
              ·
                refine ⟨54018688222903941243478421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36012458815269294162318947 54018688222903941243478421)
                ·
                  refine ⟨2532126010448622245788051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54018688222903941243478421 2532126010448622245788051)
                  ·
                    refine ⟨3798189015672933368682077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2532126010448622245788051 3798189015672933368682077)
                    ·
                      refine ⟨1424320880877350013255779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3798189015672933368682077 1424320880877350013255779)
                      ·
                        rfl

theorem cell23_2773855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_2773855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773855 prefixEnd_2773855 := by exact prefixLift 2773855
  have htrace : WordTrace (prefixWord ++ tailWord_2773855) baseStart_2773855 baseEnd_2773855 := by
    simpa [prefixWord, tailWord_2773855, baseEnd_2773855] using wordTrace_append hprefix tailTrace_2773855
  have hstable : (prefixWord ++ tailWord_2773855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773855).length < 2 ^ (prefixWord ++ tailWord_2773855).sum := by decide
  have hdescent : baseEnd_2773855 < baseStart_2773855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773865 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 7, 3, 2]
def baseStart_2773865 : Nat := 118140960795 + 2773865 * 2 ^ 59
def prefixEnd_2773865 : Nat := 4983230072969 + 3 ^ 40 * 2773865 * 2
def baseEnd_2773865 : Nat := 1424326015683894974130733

theorem tailTrace_2773865 : CollatzResearch.WordTrace tailWord_2773865 prefixEnd_2773865 1424326015683894974130733 := by
  unfold tailWord_2773865
  simp only [CollatzResearch.WordTrace]
  refine ⟨101171168095768318270867049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67447445397178878847244699 101171168095768318270867049)
  ·
    refine ⟨75878376071826238703150287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101171168095768318270867049 75878376071826238703150287)
    ·
      refine ⟨113817564107739358054725431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75878376071826238703150287 113817564107739358054725431)
      ·
        refine ⟨170726346161609037082088147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113817564107739358054725431 170726346161609037082088147)
        ·
          refine ⟨256089519242413555623132221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170726346161609037082088147 256089519242413555623132221)
          ·
            refine ⟨96033569715905083358674583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256089519242413555623132221 96033569715905083358674583)
            ·
              refine ⟨144050354573857625038011875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96033569715905083358674583 144050354573857625038011875)
              ·
                refine ⟨216075531860786437557017813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144050354573857625038011875 216075531860786437557017813)
                ·
                  refine ⟨5064270277987182130242605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 216075531860786437557017813 5064270277987182130242605)
                  ·
                    refine ⟨1899101354245193298840977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5064270277987182130242605 1899101354245193298840977)
                    ·
                      refine ⟨1424326015683894974130733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1899101354245193298840977 1424326015683894974130733)
                      ·
                        rfl

theorem cell23_2773865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 3, 2].length) (baseStart_2773865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773865 prefixEnd_2773865 := by exact prefixLift 2773865
  have htrace : WordTrace (prefixWord ++ tailWord_2773865) baseStart_2773865 baseEnd_2773865 := by
    simpa [prefixWord, tailWord_2773865, baseEnd_2773865] using wordTrace_append hprefix tailTrace_2773865
  have hstable : (prefixWord ++ tailWord_2773865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773865).length < 2 ^ (prefixWord ++ tailWord_2773865).sum := by decide
  have hdescent : baseEnd_2773865 < baseStart_2773865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773868 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 5]
def baseStart_2773868 : Nat := 118140960795 + 2773868 * 2 ^ 59
def prefixEnd_2773868 : Nat := 4983230072969 + 3 ^ 40 * 2773868 * 2
def baseEnd_2773868 : Nat := 1424327556125858462393219

theorem tailTrace_2773868 : CollatzResearch.WordTrace tailWord_2773868 prefixEnd_2773868 1424327556125858462393219 := by
  unfold tailWord_2773868
  simp only [CollatzResearch.WordTrace]
  refine ⟨50585638757378724891613129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67447518343171633188817505 50585638757378724891613129)
  ·
    refine ⟨37939229068034043668709847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50585638757378724891613129 37939229068034043668709847)
    ·
      refine ⟨56908843602051065503064771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37939229068034043668709847 56908843602051065503064771)
      ·
        refine ⟨85363265403076598254597157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56908843602051065503064771 85363265403076598254597157)
        ·
          refine ⟨16005612263076862172736967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85363265403076598254597157 16005612263076862172736967)
          ·
            refine ⟨24008418394615293259105451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16005612263076862172736967 24008418394615293259105451)
            ·
              refine ⟨36012627591922939888658177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24008418394615293259105451 36012627591922939888658177)
              ·
                refine ⟨27009470693942204916493633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36012627591922939888658177 27009470693942204916493633)
                ·
                  refine ⟨20257103020456653687370225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27009470693942204916493633 20257103020456653687370225)
                  ·
                    refine ⟨15192827265342490265527669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20257103020456653687370225 15192827265342490265527669)
                    ·
                      refine ⟨1424327556125858462393219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15192827265342490265527669 1424327556125858462393219)
                      ·
                        rfl

theorem cell23_2773868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_2773868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773868 prefixEnd_2773868 := by exact prefixLift 2773868
  have htrace : WordTrace (prefixWord ++ tailWord_2773868) baseStart_2773868 baseEnd_2773868 := by
    simpa [prefixWord, tailWord_2773868, baseEnd_2773868] using wordTrace_append hprefix tailTrace_2773868
  have hstable : (prefixWord ++ tailWord_2773868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773868).length < 2 ^ (prefixWord ++ tailWord_2773868).sum := by decide
  have hdescent : baseEnd_2773868 < baseStart_2773868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773929 : List Nat := [1, 2, 1, 1, 1, 1, 8, 2, 2, 2, 2]
def baseStart_2773929 : Nat := 118140960795 + 2773929 * 2 ^ 59
def prefixEnd_2773929 : Nat := 4983230072969 + 3 ^ 40 * 2773929 * 2
def baseEnd_2773929 : Nat := 1424358878445782723730439

theorem tailTrace_2773929 : CollatzResearch.WordTrace tailWord_2773929 prefixEnd_2773929 1424358878445782723730439 := by
  unfold tailWord_2773929
  simp only [CollatzResearch.WordTrace]
  refine ⟨101173502367536457201196841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67449001578357638134131227 101173502367536457201196841)
  ·
    refine ⟨75880126775652342900897631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101173502367536457201196841 75880126775652342900897631)
    ·
      refine ⟨113820190163478514351346447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75880126775652342900897631 113820190163478514351346447)
      ·
        refine ⟨170730285245217771527019671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113820190163478514351346447 170730285245217771527019671)
        ·
          refine ⟨256095427867826657290529507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170730285245217771527019671 256095427867826657290529507)
          ·
            refine ⟨384143141801739985935794261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256095427867826657290529507 384143141801739985935794261)
            ·
              refine ⟨4501677442989140460185089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 384143141801739985935794261 4501677442989140460185089)
              ·
                refine ⟨3376258082241855345138817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4501677442989140460185089 3376258082241855345138817)
                ·
                  refine ⟨2532193561681391508854113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3376258082241855345138817 2532193561681391508854113)
                  ·
                    refine ⟨1899145171261043631640585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2532193561681391508854113 1899145171261043631640585)
                    ·
                      refine ⟨1424358878445782723730439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1899145171261043631640585 1424358878445782723730439)
                      ·
                        rfl

theorem cell23_2773929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2, 2, 2].length) (baseStart_2773929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773929 prefixEnd_2773929 := by exact prefixLift 2773929
  have htrace : WordTrace (prefixWord ++ tailWord_2773929) baseStart_2773929 baseEnd_2773929 := by
    simpa [prefixWord, tailWord_2773929, baseEnd_2773929] using wordTrace_append hprefix tailTrace_2773929
  have hstable : (prefixWord ++ tailWord_2773929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773929).length < 2 ^ (prefixWord ++ tailWord_2773929).sum := by decide
  have hdescent : baseEnd_2773929 < baseStart_2773929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773938 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8]
def baseStart_2773938 : Nat := 118140960795 + 2773938 * 2 ^ 59
def prefixEnd_2773938 : Nat := 4983230072969 + 3 ^ 40 * 2773938 * 2
def baseEnd_2773938 : Nat := 1424363499771673188517897

theorem tailTrace_2773938 : CollatzResearch.WordTrace tailWord_2773938 prefixEnd_2773938 1424363499771673188517897 := by
  unfold tailWord_2773938
  simp only [CollatzResearch.WordTrace]
  refine ⟨25293457656125962934568617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67449220416335901158849645 25293457656125962934568617)
  ·
    refine ⟨18970093242094472200926463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25293457656125962934568617 18970093242094472200926463)
    ·
      refine ⟨28455139863141708301389695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18970093242094472200926463 28455139863141708301389695)
      ·
        refine ⟨42682709794712562452084543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28455139863141708301389695 42682709794712562452084543)
        ·
          refine ⟨64024064692068843678126815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42682709794712562452084543 64024064692068843678126815)
          ·
            refine ⟨96036097038103265517190223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64024064692068843678126815 96036097038103265517190223)
            ·
              refine ⟨144054145557154898275785335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96036097038103265517190223 144054145557154898275785335)
              ·
                refine ⟨216081218335732347413678003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144054145557154898275785335 216081218335732347413678003)
                ·
                  refine ⟨324121827503598521120517005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216081218335732347413678003 324121827503598521120517005)
                  ·
                    refine ⟨121545685313849445420193877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 324121827503598521120517005 121545685313849445420193877)
                    ·
                      refine ⟨1424363499771673188517897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 121545685313849445420193877 1424363499771673188517897)
                      ·
                        rfl

theorem cell23_2773938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_2773938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773938 prefixEnd_2773938 := by exact prefixLift 2773938
  have htrace : WordTrace (prefixWord ++ tailWord_2773938) baseStart_2773938 baseEnd_2773938 := by
    simpa [prefixWord, tailWord_2773938, baseEnd_2773938] using wordTrace_append hprefix tailTrace_2773938
  have hstable : (prefixWord ++ tailWord_2773938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773938).length < 2 ^ (prefixWord ++ tailWord_2773938).sum := by decide
  have hdescent : baseEnd_2773938 < baseStart_2773938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773945 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 1, 5, 3]
def baseStart_2773945 : Nat := 118140960795 + 2773945 * 2 ^ 59
def prefixEnd_2773945 : Nat := 4983230072969 + 3 ^ 40 * 2773945 * 2
def baseEnd_2773945 : Nat := 1424367094136254661130365

theorem tailTrace_2773945 : CollatzResearch.WordTrace tailWord_2773945 prefixEnd_2773945 1424367094136254661130365 := by
  unfold tailWord_2773945
  simp only [CollatzResearch.WordTrace]
  refine ⟨101174085935478491933779289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67449390623652327955852859 101174085935478491933779289)
  ·
    refine ⟨75880564451608868950334467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101174085935478491933779289 75880564451608868950334467)
    ·
      refine ⟨113820846677413303425501701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75880564451608868950334467 113820846677413303425501701)
      ·
        refine ⟨21341408752014994392281569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113820846677413303425501701 21341408752014994392281569)
        ·
          refine ⟨16006056564011245794211177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21341408752014994392281569 16006056564011245794211177)
          ·
            refine ⟨12004542423008434345658383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16006056564011245794211177 12004542423008434345658383)
            ·
              refine ⟨18006813634512651518487575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12004542423008434345658383 18006813634512651518487575)
              ·
                refine ⟨27010220451768977277731363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18006813634512651518487575 27010220451768977277731363)
                ·
                  refine ⟨40515330677653465916597045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27010220451768977277731363 40515330677653465916597045)
                  ·
                    refine ⟨3798312251030012429680973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40515330677653465916597045 3798312251030012429680973)
                    ·
                      refine ⟨1424367094136254661130365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3798312251030012429680973 1424367094136254661130365)
                      ·
                        rfl

theorem cell23_2773945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_2773945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773945 prefixEnd_2773945 := by exact prefixLift 2773945
  have htrace : WordTrace (prefixWord ++ tailWord_2773945) baseStart_2773945 baseEnd_2773945 := by
    simpa [prefixWord, tailWord_2773945, baseEnd_2773945] using wordTrace_append hprefix tailTrace_2773945
  have hstable : (prefixWord ++ tailWord_2773945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773945).length < 2 ^ (prefixWord ++ tailWord_2773945).sum := by decide
  have hdescent : baseEnd_2773945 < baseStart_2773945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773985 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 4, 1, 4]
def baseStart_2773985 : Nat := 118140960795 + 2773985 * 2 ^ 59
def prefixEnd_2773985 : Nat := 4983230072969 + 3 ^ 40 * 2773985 * 2
def baseEnd_2773985 : Nat := 1424387633362434504630181

theorem tailTrace_2773985 : CollatzResearch.WordTrace tailWord_2773985 prefixEnd_2773985 1424387633362434504630181 := by
  unfold tailWord_2773985
  simp only [CollatzResearch.WordTrace]
  refine ⟨101175544855333578765235409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67450363236889052510156939 101175544855333578765235409)
  ·
    refine ⟨75881658641500184073926557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101175544855333578765235409 75881658641500184073926557)
    ·
      refine ⟨28455621990562569027722459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75881658641500184073926557 28455621990562569027722459)
      ·
        refine ⟨42683432985843853541583689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28455621990562569027722459 42683432985843853541583689)
        ·
          refine ⟨32012574739382890156187767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42683432985843853541583689 32012574739382890156187767)
          ·
            refine ⟨48018862109074335234281651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32012574739382890156187767 48018862109074335234281651)
            ·
              refine ⟨72028293163611502851422477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48018862109074335234281651 72028293163611502851422477)
              ·
                refine ⟨27010609936354313569283429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72028293163611502851422477 27010609936354313569283429)
                ·
                  refine ⟨5064489363066433794240643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27010609936354313569283429 5064489363066433794240643)
                  ·
                    refine ⟨7596734044599650691360965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5064489363066433794240643 7596734044599650691360965)
                    ·
                      refine ⟨1424387633362434504630181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7596734044599650691360965 1424387633362434504630181)
                      ·
                        rfl

theorem cell23_2773985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_2773985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2773985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2773985 prefixEnd_2773985 := by exact prefixLift 2773985
  have htrace : WordTrace (prefixWord ++ tailWord_2773985) baseStart_2773985 baseEnd_2773985 := by
    simpa [prefixWord, tailWord_2773985, baseEnd_2773985] using wordTrace_append hprefix tailTrace_2773985
  have hstable : (prefixWord ++ tailWord_2773985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773985).length < 2 ^ (prefixWord ++ tailWord_2773985).sum := by decide
  have hdescent : baseEnd_2773985 < baseStart_2773985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774012 : List Nat := [2, 2, 2, 1, 2, 3, 2, 2, 3, 4]
def baseStart_2774012 : Nat := 118140960795 + 2774012 * 2 ^ 59
def prefixEnd_2774012 : Nat := 4983230072969 + 3 ^ 40 * 2774012 * 2
def baseEnd_2774012 : Nat := 474800499113368632997519

theorem tailTrace_2774012 : CollatzResearch.WordTrace tailWord_2774012 prefixEnd_2774012 474800499113368632997519 := by
  unfold tailWord_2774012
  simp only [CollatzResearch.WordTrace]
  refine ⟨50588264813117881188234145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67451019750823841584312193 50588264813117881188234145)
  ·
    refine ⟨37941198609838410891175609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50588264813117881188234145 37941198609838410891175609)
    ·
      refine ⟨28455898957378808168381707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37941198609838410891175609 28455898957378808168381707)
      ·
        refine ⟨42683848436068212252572561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28455898957378808168381707 42683848436068212252572561)
        ·
          refine ⟨32012886327051159189429421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42683848436068212252572561 32012886327051159189429421)
          ·
            refine ⟨12004832372644184696036033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32012886327051159189429421 12004832372644184696036033)
            ·
              refine ⟨9003624279483138522027025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12004832372644184696036033 9003624279483138522027025)
              ·
                refine ⟨6752718209612353891520269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9003624279483138522027025 6752718209612353891520269)
                ·
                  refine ⟨2532269328604632709320101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6752718209612353891520269 2532269328604632709320101)
                  ·
                    refine ⟨474800499113368632997519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2532269328604632709320101 474800499113368632997519)
                    ·
                      rfl

theorem cell23_2774012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_2774012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774012 prefixEnd_2774012 := by exact prefixLift 2774012
  have htrace : WordTrace (prefixWord ++ tailWord_2774012) baseStart_2774012 baseEnd_2774012 := by
    simpa [prefixWord, tailWord_2774012, baseEnd_2774012] using wordTrace_append hprefix tailTrace_2774012
  have hstable : (prefixWord ++ tailWord_2774012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774012).length < 2 ^ (prefixWord ++ tailWord_2774012).sum := by decide
  have hdescent : baseEnd_2774012 < baseStart_2774012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774039 : List Nat := [1, 1, 3, 5, 1, 2, 1, 2, 2, 2, 3]
def baseStart_2774039 : Nat := 118140960795 + 2774039 * 2 ^ 59
def prefixEnd_2774039 : Nat := 4983230072969 + 3 ^ 40 * 2774039 * 2
def baseEnd_2774039 : Nat := 1424415361317777293354933

theorem tailTrace_2774039 : CollatzResearch.WordTrace tailWord_2774039 prefixEnd_2774039 1424415361317777293354933 := by
  unfold tailWord_2774039
  simp only [CollatzResearch.WordTrace]
  refine ⟨101177514397137945987701171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67451676264758630658467447 101177514397137945987701171)
  ·
    refine ⟨151766271595706918981551757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101177514397137945987701171 151766271595706918981551757)
    ·
      refine ⟨56912351848390094618081909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151766271595706918981551757 56912351848390094618081909)
      ·
        refine ⟨5335532985786571370445179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56912351848390094618081909 5335532985786571370445179)
        ·
          refine ⟨8003299478679857055667769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5335532985786571370445179 8003299478679857055667769)
          ·
            refine ⟨6002474609009892791750827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8003299478679857055667769 6002474609009892791750827)
            ·
              refine ⟨9003711913514839187626241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6002474609009892791750827 9003711913514839187626241)
              ·
                refine ⟨6752783935136129390719681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9003711913514839187626241 6752783935136129390719681)
                ·
                  refine ⟨5064587951352097043039761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6752783935136129390719681 5064587951352097043039761)
                  ·
                    refine ⟨3798440963514072782279821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5064587951352097043039761 3798440963514072782279821)
                    ·
                      refine ⟨1424415361317777293354933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3798440963514072782279821 1424415361317777293354933)
                      ·
                        rfl

theorem cell23_2774039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_2774039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774039 prefixEnd_2774039 := by exact prefixLift 2774039
  have htrace : WordTrace (prefixWord ++ tailWord_2774039) baseStart_2774039 baseEnd_2774039 := by
    simpa [prefixWord, tailWord_2774039, baseEnd_2774039] using wordTrace_append hprefix tailTrace_2774039
  have hstable : (prefixWord ++ tailWord_2774039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774039).length < 2 ^ (prefixWord ++ tailWord_2774039).sum := by decide
  have hdescent : baseEnd_2774039 < baseStart_2774039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774072 : List Nat := [2, 1, 2, 1, 5, 2, 1, 1, 3, 5]
def baseStart_2774072 : Nat := 118140960795 + 2774072 * 2 ^ 59
def prefixEnd_2774072 : Nat := 4983230072969 + 3 ^ 40 * 2774072 * 2
def baseEnd_2774072 : Nat := 474810768726458554747427

theorem tailTrace_2774072 : CollatzResearch.WordTrace tailWord_2774072 prefixEnd_2774072 474810768726458554747427 := by
  unfold tailWord_2774072
  simp only [CollatzResearch.WordTrace]
  refine ⟨50589359003009196311826235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67452478670678928415768313 50589359003009196311826235)
  ·
    refine ⟨75884038504513794467739353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50589359003009196311826235 75884038504513794467739353)
    ·
      refine ⟨56913028878385345850804515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75884038504513794467739353 56913028878385345850804515)
      ·
        refine ⟨85369543317578018776206773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56913028878385345850804515 85369543317578018776206773)
        ·
          refine ⟨8003394686022939260269385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85369543317578018776206773 8003394686022939260269385)
          ·
            refine ⟨6002546014517204445202039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8003394686022939260269385 6002546014517204445202039)
            ·
              refine ⟨9003819021775806667803059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6002546014517204445202039 9003819021775806667803059)
              ·
                refine ⟨13505728532663710001704589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9003819021775806667803059 13505728532663710001704589)
                ·
                  refine ⟨5064648199748891250639221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13505728532663710001704589 5064648199748891250639221)
                  ·
                    refine ⟨474810768726458554747427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5064648199748891250639221 474810768726458554747427)
                    ·
                      rfl

theorem cell23_2774072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 3, 5].length) (baseStart_2774072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774072 prefixEnd_2774072 := by exact prefixLift 2774072
  have htrace : WordTrace (prefixWord ++ tailWord_2774072) baseStart_2774072 baseEnd_2774072 := by
    simpa [prefixWord, tailWord_2774072, baseEnd_2774072] using wordTrace_append hprefix tailTrace_2774072
  have hstable : (prefixWord ++ tailWord_2774072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774072).length < 2 ^ (prefixWord ++ tailWord_2774072).sum := by decide
  have hdescent : baseEnd_2774072 < baseStart_2774072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774085 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 3, 6]
def baseStart_2774085 : Nat := 118140960795 + 2774085 * 2 ^ 59
def prefixEnd_2774085 : Nat := 4983230072969 + 3 ^ 40 * 2774085 * 2
def baseEnd_2774085 : Nat := 474812993809294704459907

theorem tailTrace_2774085 : CollatzResearch.WordTrace tailWord_2774085 prefixEnd_2774085 474812993809294704459907 := by
  unfold tailWord_2774085
  simp only [CollatzResearch.WordTrace]
  refine ⟨101179192154971295843875709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67452794769980863895917139 101179192154971295843875709)
  ·
    refine ⟨37942197058114235941453391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101179192154971295843875709 37942197058114235941453391)
    ·
      refine ⟨56913295587171353912180087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37942197058114235941453391 56913295587171353912180087)
      ·
        refine ⟨85369943380757030868270131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56913295587171353912180087 85369943380757030868270131)
        ·
          refine ⟨128054915071135546302405197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85369943380757030868270131 128054915071135546302405197)
          ·
            refine ⟨48020593151675829863401949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128054915071135546302405197 48020593151675829863401949)
            ·
              refine ⟨18007722431878436198775731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48020593151675829863401949 18007722431878436198775731)
              ·
                refine ⟨27011583647817654298163597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18007722431878436198775731 27011583647817654298163597)
                ·
                  refine ⟨10129343867931620361811349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27011583647817654298163597 10129343867931620361811349)
                  ·
                    refine ⟨474812993809294704459907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10129343867931620361811349 474812993809294704459907)
                    ·
                      rfl

theorem cell23_2774085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 6].length) (baseStart_2774085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774085 prefixEnd_2774085 := by exact prefixLift 2774085
  have htrace : WordTrace (prefixWord ++ tailWord_2774085) baseStart_2774085 baseEnd_2774085 := by
    simpa [prefixWord, tailWord_2774085, baseEnd_2774085] using wordTrace_append hprefix tailTrace_2774085
  have hstable : (prefixWord ++ tailWord_2774085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774085).length < 2 ^ (prefixWord ++ tailWord_2774085).sum := by decide
  have hdescent : baseEnd_2774085 < baseStart_2774085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774105 : List Nat := [1, 2, 1, 2, 2, 1, 2, 4, 1, 1, 6]
def baseStart_2774105 : Nat := 118140960795 + 2774105 * 2 ^ 59
def prefixEnd_2774105 : Nat := 4983230072969 + 3 ^ 40 * 2774105 * 2
def baseEnd_2774105 : Nat := 1424449251040974035129629

theorem tailTrace_2774105 : CollatzResearch.WordTrace tailWord_2774105 prefixEnd_2774105 1424449251040974035129629 := by
  unfold tailWord_2774105
  simp only [CollatzResearch.WordTrace]
  refine ⟨101179921614898839259603769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67453281076599226173069179 101179921614898839259603769)
  ·
    refine ⟨75884941211174129444702827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101179921614898839259603769 75884941211174129444702827)
    ·
      refine ⟨113827411816761194167054241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75884941211174129444702827 113827411816761194167054241)
      ·
        refine ⟨85370558862570895625290681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113827411816761194167054241 85370558862570895625290681)
        ·
          refine ⟨64027919146928171718968011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85370558862570895625290681 64027919146928171718968011)
          ·
            refine ⟨96041878720392257578452017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64027919146928171718968011 96041878720392257578452017)
            ·
              refine ⟨72031409040294193183839013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96041878720392257578452017 72031409040294193183839013)
              ·
                refine ⟨13505889195055161221969815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72031409040294193183839013 13505889195055161221969815)
                ·
                  refine ⟨20258833792582741832954723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13505889195055161221969815 20258833792582741832954723)
                  ·
                    refine ⟨30388250688874112749432085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20258833792582741832954723 30388250688874112749432085)
                    ·
                      refine ⟨1424449251040974035129629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30388250688874112749432085 1424449251040974035129629)
                      ·
                        rfl

theorem cell23_2774105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_2774105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774105 prefixEnd_2774105 := by exact prefixLift 2774105
  have htrace : WordTrace (prefixWord ++ tailWord_2774105) baseStart_2774105 baseEnd_2774105 := by
    simpa [prefixWord, tailWord_2774105, baseEnd_2774105] using wordTrace_append hprefix tailTrace_2774105
  have hstable : (prefixWord ++ tailWord_2774105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774105).length < 2 ^ (prefixWord ++ tailWord_2774105).sum := by decide
  have hdescent : baseEnd_2774105 < baseStart_2774105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774112 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 3]
def baseStart_2774112 : Nat := 118140960795 + 2774112 * 2 ^ 59
def prefixEnd_2774112 : Nat := 4983230072969 + 3 ^ 40 * 2774112 * 2
def baseEnd_2774112 : Nat := 1424452845405555507742097

theorem tailTrace_2774112 : CollatzResearch.WordTrace tailWord_2774112 prefixEnd_2774112 1424452845405555507742097 := by
  unfold tailWord_2774112
  simp only [CollatzResearch.WordTrace]
  refine ⟨50590088462936739727554295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67453451283915652970072393 50590088462936739727554295)
  ·
    refine ⟨75885132694405109591331443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50590088462936739727554295 75885132694405109591331443)
    ·
      refine ⟨113827699041607664386997165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75885132694405109591331443 113827699041607664386997165)
      ·
        refine ⟨42685387140602874145123937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113827699041607664386997165 42685387140602874145123937)
        ·
          refine ⟨32014040355452155608842953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42685387140602874145123937 32014040355452155608842953)
          ·
            refine ⟨24010530266589116706632215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32014040355452155608842953 24010530266589116706632215)
            ·
              refine ⟨36015795399883675059948323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24010530266589116706632215 36015795399883675059948323)
              ·
                refine ⟨54023693099825512589922485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36015795399883675059948323 54023693099825512589922485)
                ·
                  refine ⟨5064721228108641805305233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54023693099825512589922485 5064721228108641805305233)
                  ·
                    refine ⟨3798540921081481353978925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5064721228108641805305233 3798540921081481353978925)
                    ·
                      refine ⟨1424452845405555507742097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3798540921081481353978925 1424452845405555507742097)
                      ·
                        rfl

theorem cell23_2774112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_2774112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774112 prefixEnd_2774112 := by exact prefixLift 2774112
  have htrace : WordTrace (prefixWord ++ tailWord_2774112) baseStart_2774112 baseEnd_2774112 := by
    simpa [prefixWord, tailWord_2774112, baseEnd_2774112] using wordTrace_append hprefix tailTrace_2774112
  have hstable : (prefixWord ++ tailWord_2774112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774112).length < 2 ^ (prefixWord ++ tailWord_2774112).sum := by decide
  have hdescent : baseEnd_2774112 < baseStart_2774112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774119 : List Nat := [1, 1, 5, 1, 1, 3, 2, 3, 2, 4]
def baseStart_2774119 : Nat := 118140960795 + 2774119 * 2 ^ 59
def prefixEnd_2774119 : Nat := 4983230072969 + 3 ^ 40 * 2774119 * 2
def baseEnd_2774119 : Nat := 474818813256712326784855

theorem tailTrace_2774119 : CollatzResearch.WordTrace tailWord_2774119 prefixEnd_2774119 474818813256712326784855 := by
  unfold tailWord_2774119
  simp only [CollatzResearch.WordTrace]
  refine ⟨101180432236848119650613411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67453621491232079767075607 101180432236848119650613411)
  ·
    refine ⟨151770648355272179475920117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101180432236848119650613411 151770648355272179475920117)
    ·
      refine ⟨14228498283306766825867511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 151770648355272179475920117 14228498283306766825867511)
      ·
        refine ⟨21342747424960150238801267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14228498283306766825867511 21342747424960150238801267)
        ·
          refine ⟨32014121137440225358201901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21342747424960150238801267 32014121137440225358201901)
          ·
            refine ⟨12005295426540084509325713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32014121137440225358201901 12005295426540084509325713)
            ·
              refine ⟨9003971569905063381994285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12005295426540084509325713 9003971569905063381994285)
              ·
                refine ⟨3376489338714398768247857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9003971569905063381994285 3376489338714398768247857)
                ·
                  refine ⟨2532367004035799076185893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3376489338714398768247857 2532367004035799076185893)
                  ·
                    refine ⟨474818813256712326784855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2532367004035799076185893 474818813256712326784855)
                    ·
                      rfl

theorem cell23_2774119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_2774119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774119 prefixEnd_2774119 := by exact prefixLift 2774119
  have htrace : WordTrace (prefixWord ++ tailWord_2774119) baseStart_2774119 baseEnd_2774119 := by
    simpa [prefixWord, tailWord_2774119, baseEnd_2774119] using wordTrace_append hprefix tailTrace_2774119
  have hstable : (prefixWord ++ tailWord_2774119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774119).length < 2 ^ (prefixWord ++ tailWord_2774119).sum := by decide
  have hdescent : baseEnd_2774119 < baseStart_2774119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774126 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 5, 2, 2]
def baseStart_2774126 : Nat := 118140960795 + 2774126 * 2 ^ 59
def prefixEnd_2774126 : Nat := 4983230072969 + 3 ^ 40 * 2774126 * 2
def baseEnd_2774126 : Nat := 1424460034134718452967033

theorem tailTrace_2774126 : CollatzResearch.WordTrace tailWord_2774126 prefixEnd_2774126 1424460034134718452967033 := by
  unfold tailWord_2774126
  simp only [CollatzResearch.WordTrace]
  refine ⟨12647585943477844980764779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67453791698548506564078821 12647585943477844980764779)
  ·
    refine ⟨18971378915216767471147169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12647585943477844980764779 18971378915216767471147169)
    ·
      refine ⟨14228534186412575603360377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18971378915216767471147169 14228534186412575603360377)
      ·
        refine ⟨10671400639809431702520283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14228534186412575603360377 10671400639809431702520283)
        ·
          refine ⟨16007100959714147553780425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10671400639809431702520283 16007100959714147553780425)
          ·
            refine ⟨12005325719785610665335319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16007100959714147553780425 12005325719785610665335319)
            ·
              refine ⟨18007988579678415998002979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12005325719785610665335319 18007988579678415998002979)
              ·
                refine ⟨27011982869517623997004469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18007988579678415998002979 27011982869517623997004469)
                ·
                  refine ⟨2532373394017277249719169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27011982869517623997004469 2532373394017277249719169)
                  ·
                    refine ⟨1899280045512957937289377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2532373394017277249719169 1899280045512957937289377)
                    ·
                      refine ⟨1424460034134718452967033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1899280045512957937289377 1424460034134718452967033)
                      ·
                        rfl

theorem cell23_2774126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_2774126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774126 prefixEnd_2774126 := by exact prefixLift 2774126
  have htrace : WordTrace (prefixWord ++ tailWord_2774126) baseStart_2774126 baseEnd_2774126 := by
    simpa [prefixWord, tailWord_2774126, baseEnd_2774126] using wordTrace_append hprefix tailTrace_2774126
  have hstable : (prefixWord ++ tailWord_2774126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774126).length < 2 ^ (prefixWord ++ tailWord_2774126).sum := by decide
  have hdescent : baseEnd_2774126 < baseStart_2774126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774185 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 9]
def baseStart_2774185 : Nat := 118140960795 + 2774185 * 2 ^ 59
def prefixEnd_2774185 : Nat := 4983230072969 + 3 ^ 40 * 2774185 * 2
def baseEnd_2774185 : Nat := 1424490329493333722129261

theorem tailTrace_2774185 : CollatzResearch.WordTrace tailWord_2774185 prefixEnd_2774185 1424490329493333722129261 := by
  unfold tailWord_2774185
  simp only [CollatzResearch.WordTrace]
  refine ⟨101182839454609012922516009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67455226303072675281677339 101182839454609012922516009)
  ·
    refine ⟨75887129590956759691887007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101182839454609012922516009 75887129590956759691887007)
    ·
      refine ⟨113830694386435139537830511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75887129590956759691887007 113830694386435139537830511)
      ·
        refine ⟨170746041579652709306745767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113830694386435139537830511 170746041579652709306745767)
        ·
          refine ⟨256119062369479063960118651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170746041579652709306745767 256119062369479063960118651)
          ·
            refine ⟨384178593554218595940177977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256119062369479063960118651 384178593554218595940177977)
            ·
              refine ⟨288133945165663946955133483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 384178593554218595940177977 288133945165663946955133483)
              ·
                refine ⟨432200917748495920432700225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288133945165663946955133483 432200917748495920432700225)
                ·
                  refine ⟨324150688311371940324525169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 432200917748495920432700225 324150688311371940324525169)
                  ·
                    refine ⟨243113016233528955243393877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 324150688311371940324525169 243113016233528955243393877)
                    ·
                      refine ⟨1424490329493333722129261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 243113016233528955243393877 1424490329493333722129261)
                      ·
                        rfl

theorem cell23_2774185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_2774185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774185 prefixEnd_2774185 := by exact prefixLift 2774185
  have htrace : WordTrace (prefixWord ++ tailWord_2774185) baseStart_2774185 baseEnd_2774185 := by
    simpa [prefixWord, tailWord_2774185, baseEnd_2774185] using wordTrace_append hprefix tailTrace_2774185
  have hstable : (prefixWord ++ tailWord_2774185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774185).length < 2 ^ (prefixWord ++ tailWord_2774185).sum := by decide
  have hdescent : baseEnd_2774185 < baseStart_2774185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774199 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 3, 4, 2]
def baseStart_2774199 : Nat := 118140960795 + 2774199 * 2 ^ 59
def prefixEnd_2774199 : Nat := 4983230072969 + 3 ^ 40 * 2774199 * 2
def baseEnd_2774199 : Nat := 1424497518222496667354197

theorem tailTrace_2774199 : CollatzResearch.WordTrace tailWord_2774199 prefixEnd_2774199 1424497518222496667354197 := by
  unfold tailWord_2774199
  simp only [CollatzResearch.WordTrace]
  refine ⟨101183350076558293313525651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67455566717705528875683767 101183350076558293313525651)
  ·
    refine ⟨151775025114837439970288477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101183350076558293313525651 151775025114837439970288477)
    ·
      refine ⟨56915634418064039988858179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151775025114837439970288477 56915634418064039988858179)
      ·
        refine ⟨85373451627096059983287269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56915634418064039988858179 85373451627096059983287269)
        ·
          refine ⟨16007522180080511246866363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85373451627096059983287269 16007522180080511246866363)
          ·
            refine ⟨24011283270120766870299545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16007522180080511246866363 24011283270120766870299545)
            ·
              refine ⟨18008462452590575152724659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24011283270120766870299545 18008462452590575152724659)
              ·
                refine ⟨27012693678885862729086989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18008462452590575152724659 27012693678885862729086989)
                ·
                  refine ⟨10129760129582198523407621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27012693678885862729086989 10129760129582198523407621)
                  ·
                    refine ⟨1899330024296662223138929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10129760129582198523407621 1899330024296662223138929)
                    ·
                      refine ⟨1424497518222496667354197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1899330024296662223138929 1424497518222496667354197)
                      ·
                        rfl

theorem cell23_2774199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 4, 2].length) (baseStart_2774199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774199 prefixEnd_2774199 := by exact prefixLift 2774199
  have htrace : WordTrace (prefixWord ++ tailWord_2774199) baseStart_2774199 baseEnd_2774199 := by
    simpa [prefixWord, tailWord_2774199, baseEnd_2774199] using wordTrace_append hprefix tailTrace_2774199
  have hstable : (prefixWord ++ tailWord_2774199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774199).length < 2 ^ (prefixWord ++ tailWord_2774199).sum := by decide
  have hdescent : baseEnd_2774199 < baseStart_2774199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
