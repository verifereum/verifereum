Theory vfmTest0919[no_sig_docs]
Ancestors vfmTestDefs0919
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0919_0.nsv"];
val thyn = "vfmTestDefs0919";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
