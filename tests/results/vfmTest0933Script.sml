Theory vfmTest0933[no_sig_docs]
Ancestors vfmTestDefs0933
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0933_0.nsv"];
val thyn = "vfmTestDefs0933";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
