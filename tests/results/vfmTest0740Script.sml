Theory vfmTest0740[no_sig_docs]
Ancestors vfmTestDefs0740
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0740_0.nsv"];
val thyn = "vfmTestDefs0740";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
