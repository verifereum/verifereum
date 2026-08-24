Theory vfmTest0040[no_sig_docs]
Ancestors vfmTestDefs0040
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0040_0.nsv", "result0040_1.nsv", "result0040_2.nsv", "result0040_3.nsv", "result0040_4.nsv", "result0040_5.nsv", "result0040_6.nsv", "result0040_7.nsv", "result0040_8.nsv", "result0040_9.nsv"];
val thyn = "vfmTestDefs0040";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
