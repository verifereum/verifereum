Theory vfmTest0683[no_sig_docs]
Ancestors vfmTestDefs0683
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0683_0.nsv"];
val thyn = "vfmTestDefs0683";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
