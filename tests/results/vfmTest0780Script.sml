Theory vfmTest0780[no_sig_docs]
Ancestors vfmTestDefs0780
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0780_0.nsv", "result0780_1.nsv"];
val thyn = "vfmTestDefs0780";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
