Theory vfmTest0135[no_sig_docs]
Ancestors vfmTestDefs0135
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0135_0.nsv", "result0135_1.nsv", "result0135_2.nsv"];
val thyn = "vfmTestDefs0135";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
