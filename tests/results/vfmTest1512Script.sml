Theory vfmTest1512[no_sig_docs]
Ancestors vfmTestDefs1512
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1512_0.nsv", "result1512_1.nsv", "result1512_2.nsv", "result1512_3.nsv", "result1512_4.nsv", "result1512_5.nsv", "result1512_6.nsv", "result1512_7.nsv"];
val thyn = "vfmTestDefs1512";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
