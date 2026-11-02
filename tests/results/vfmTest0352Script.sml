Theory vfmTest0352[no_sig_docs]
Ancestors vfmTestDefs0352
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0352_0.nsv", "result0352_1.nsv", "result0352_2.nsv", "result0352_3.nsv", "result0352_4.nsv", "result0352_5.nsv", "result0352_6.nsv", "result0352_7.nsv"];
val thyn = "vfmTestDefs0352";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
