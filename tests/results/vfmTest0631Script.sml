Theory vfmTest0631[no_sig_docs]
Ancestors vfmTestDefs0631
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0631_0.nsv", "result0631_1.nsv"];
val thyn = "vfmTestDefs0631";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
