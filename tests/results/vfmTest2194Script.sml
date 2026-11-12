Theory vfmTest2194[no_sig_docs]
Ancestors vfmTestDefs2194
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2194_0.nsv", "result2194_1.nsv", "result2194_2.nsv", "result2194_3.nsv", "result2194_4.nsv", "result2194_5.nsv", "result2194_6.nsv"];
val thyn = "vfmTestDefs2194";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
