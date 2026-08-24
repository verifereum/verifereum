Theory vfmTest0178[no_sig_docs]
Ancestors vfmTestDefs0178
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0178_0.nsv"];
val thyn = "vfmTestDefs0178";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
