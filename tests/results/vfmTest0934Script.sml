Theory vfmTest0934[no_sig_docs]
Ancestors vfmTestDefs0934
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0934_0.nsv"];
val thyn = "vfmTestDefs0934";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
