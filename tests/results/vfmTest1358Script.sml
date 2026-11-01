Theory vfmTest1358[no_sig_docs]
Ancestors vfmTestDefs1358
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1358_0.nsv", "result1358_1.nsv", "result1358_2.nsv", "result1358_3.nsv", "result1358_4.nsv", "result1358_5.nsv", "result1358_6.nsv", "result1358_7.nsv"];
val thyn = "vfmTestDefs1358";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
