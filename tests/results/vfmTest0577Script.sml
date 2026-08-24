Theory vfmTest0577[no_sig_docs]
Ancestors vfmTestDefs0577
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0577_0.nsv", "result0577_1.nsv"];
val thyn = "vfmTestDefs0577";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
