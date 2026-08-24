Theory vfmTest0246[no_sig_docs]
Ancestors vfmTestDefs0246
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0246_0.nsv", "result0246_1.nsv"];
val thyn = "vfmTestDefs0246";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
