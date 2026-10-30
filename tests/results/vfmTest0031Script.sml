Theory vfmTest0031[no_sig_docs]
Ancestors vfmTestDefs0031
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0031_0.nsv", "result0031_1.nsv", "result0031_2.nsv", "result0031_3.nsv", "result0031_4.nsv", "result0031_5.nsv"];
val thyn = "vfmTestDefs0031";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
