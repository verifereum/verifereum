Theory vfmTest0280[no_sig_docs]
Ancestors vfmTestDefs0280
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0280_0.nsv", "result0280_1.nsv", "result0280_2.nsv", "result0280_3.nsv", "result0280_4.nsv", "result0280_5.nsv", "result0280_6.nsv"];
val thyn = "vfmTestDefs0280";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
