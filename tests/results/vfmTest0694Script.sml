Theory vfmTest0694[no_sig_docs]
Ancestors vfmTestDefs0694
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0694_0.nsv"];
val thyn = "vfmTestDefs0694";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
