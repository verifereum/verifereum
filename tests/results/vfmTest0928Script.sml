Theory vfmTest0928[no_sig_docs]
Ancestors vfmTestDefs0928
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0928_0.nsv"];
val thyn = "vfmTestDefs0928";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
