Theory vfmTest0054[no_sig_docs]
Ancestors vfmTestDefs0054
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0054_0.nsv", "result0054_1.nsv", "result0054_2.nsv", "result0054_3.nsv", "result0054_4.nsv", "result0054_5.nsv"];
val thyn = "vfmTestDefs0054";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
