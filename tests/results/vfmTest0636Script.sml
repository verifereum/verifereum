Theory vfmTest0636[no_sig_docs]
Ancestors vfmTestDefs0636
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0636_0.nsv"];
val thyn = "vfmTestDefs0636";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
