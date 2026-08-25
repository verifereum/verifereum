Theory vfmTest0444[no_sig_docs]
Ancestors vfmTestDefs0444
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0444_0.nsv", "result0444_1.nsv", "result0444_2.nsv", "result0444_3.nsv", "result0444_4.nsv"];
val thyn = "vfmTestDefs0444";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
