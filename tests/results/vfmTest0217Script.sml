Theory vfmTest0217[no_sig_docs]
Ancestors vfmTestDefs0217
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0217_0.nsv", "result0217_1.nsv", "result0217_2.nsv", "result0217_3.nsv"];
val thyn = "vfmTestDefs0217";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
