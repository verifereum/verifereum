Theory vfmTest2119[no_sig_docs]
Ancestors vfmTestDefs2119
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2119_0.nsv", "result2119_1.nsv", "result2119_2.nsv", "result2119_3.nsv", "result2119_4.nsv", "result2119_5.nsv", "result2119_6.nsv", "result2119_7.nsv", "result2119_8.nsv", "result2119_9.nsv"];
val thyn = "vfmTestDefs2119";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
