Theory vfmTest0490[no_sig_docs]
Ancestors vfmTestDefs0490
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0490_0.nsv", "result0490_1.nsv"];
val thyn = "vfmTestDefs0490";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
