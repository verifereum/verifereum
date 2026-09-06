Theory vfmTest0760[no_sig_docs]
Ancestors vfmTestDefs0760
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0760_0.nsv", "result0760_1.nsv", "result0760_2.nsv", "result0760_3.nsv", "result0760_4.nsv", "result0760_5.nsv", "result0760_6.nsv", "result0760_7.nsv"];
val thyn = "vfmTestDefs0760";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
