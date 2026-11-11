Theory vfmTest0523[no_sig_docs]
Ancestors vfmTestDefs0523
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0523_0.nsv", "result0523_1.nsv", "result0523_2.nsv", "result0523_3.nsv", "result0523_4.nsv", "result0523_5.nsv", "result0523_6.nsv", "result0523_7.nsv"];
val thyn = "vfmTestDefs0523";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
