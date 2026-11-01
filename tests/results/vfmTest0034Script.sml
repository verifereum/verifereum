Theory vfmTest0034[no_sig_docs]
Ancestors vfmTestDefs0034
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0034_0.nsv", "result0034_1.nsv", "result0034_2.nsv", "result0034_3.nsv", "result0034_4.nsv", "result0034_5.nsv"];
val thyn = "vfmTestDefs0034";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
