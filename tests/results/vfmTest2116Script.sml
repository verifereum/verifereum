Theory vfmTest2116[no_sig_docs]
Ancestors vfmTestDefs2116
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2116_0.nsv", "result2116_1.nsv", "result2116_2.nsv", "result2116_3.nsv", "result2116_4.nsv", "result2116_5.nsv", "result2116_6.nsv", "result2116_7.nsv"];
val thyn = "vfmTestDefs2116";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
