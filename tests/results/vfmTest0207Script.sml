Theory vfmTest0207[no_sig_docs]
Ancestors vfmTestDefs0207
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0207_0.nsv", "result0207_1.nsv", "result0207_2.nsv", "result0207_3.nsv", "result0207_4.nsv", "result0207_5.nsv", "result0207_6.nsv", "result0207_7.nsv", "result0207_8.nsv", "result0207_9.nsv", "result0207_10.nsv", "result0207_11.nsv", "result0207_12.nsv", "result0207_13.nsv", "result0207_14.nsv", "result0207_15.nsv", "result0207_16.nsv", "result0207_17.nsv", "result0207_18.nsv", "result0207_19.nsv", "result0207_20.nsv", "result0207_21.nsv", "result0207_22.nsv", "result0207_23.nsv", "result0207_24.nsv"];
val thyn = "vfmTestDefs0207";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
