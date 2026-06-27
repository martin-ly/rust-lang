from typing import Optional

__all__ = ['__version__', 'debug', 'cuda', 'git_version', 'hip', 'rocm', 'xpu']
__version__ = '2.12.1+cpu'
debug = False
cuda: Optional[str] = None
git_version = '7269437d655783a26cba32aa88195b741ff496aa'
hip: Optional[str] = None
rocm: Optional[str] = None
xpu: Optional[str] = None
