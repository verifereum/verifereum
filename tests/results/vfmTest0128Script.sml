Theory vfmTest0128[no_sig_docs]
Ancestors vfmTestDefs0128
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0128_0.nsv", "result0128_1.nsv", "result0128_2.nsv", "result0128_3.nsv", "result0128_4.nsv", "result0128_5.nsv", "result0128_6.nsv", "result0128_7.nsv"];
val thyn = "vfmTestDefs0128";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
