Theory vfmTest1940[no_sig_docs]
Ancestors vfmTestDefs1940
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1940_0.nsv", "result1940_1.nsv", "result1940_2.nsv", "result1940_3.nsv", "result1940_4.nsv", "result1940_5.nsv", "result1940_6.nsv", "result1940_7.nsv"];
val thyn = "vfmTestDefs1940";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
