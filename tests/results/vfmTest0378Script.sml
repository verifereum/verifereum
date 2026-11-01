Theory vfmTest0378[no_sig_docs]
Ancestors vfmTestDefs0378
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0378_0.nsv", "result0378_1.nsv", "result0378_2.nsv", "result0378_3.nsv", "result0378_4.nsv", "result0378_5.nsv", "result0378_6.nsv", "result0378_7.nsv"];
val thyn = "vfmTestDefs0378";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
