Theory vfmTest0771[no_sig_docs]
Ancestors vfmTestDefs0771
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0771_0.nsv"];
val thyn = "vfmTestDefs0771";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
