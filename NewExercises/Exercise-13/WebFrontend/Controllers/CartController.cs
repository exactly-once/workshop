using System.Diagnostics;
using System.Threading.Tasks;
using Microsoft.AspNetCore.Mvc;
using Orders.Models;

namespace Orders.Controllers
{
    public class CartController : Controller
    {
        readonly ApplicationServices appServices;

        public CartController(ApplicationServices appServices)
        {
            this.appServices = appServices;
        }

        [Route("cart/{customerId}/{cartId}")]
        [HttpGet]
        public async Task<IActionResult> Index(string customerId, string cartId)
        {
            var cart = await appServices.Get(customerId, cartId);
            return View(cart);
        }

        [Route("cart/add-item/{customerId}/{cartId}")]
        [HttpGet]
        public IActionResult AddItem(string customerId, string cartId)
        {
            return View();
        }

        [Route("cart/add-item/{customerId}/{cartId}")]
        [HttpPost]
        public async Task<IActionResult> AddItem(string customerId, string cartId, ItemModel item)
        {
            await appServices.AddItem(customerId, cartId, item.Filling);

            return RedirectToAction("Index", new { customerId, cartId });
        }

        [Route("cart/submit/{customerId}/{cartId}")]
        [HttpPost]
        public async Task<IActionResult> Submit(string customerId, string cartId)
        {
            await appServices.SubmitOrder(customerId, cartId);

            return RedirectToAction("Index", "Orders", new { customerId });
        }

        [ResponseCache(Duration = 0, Location = ResponseCacheLocation.None, NoStore = true)]
        public IActionResult Error()
        {
            return View(new ErrorViewModel { RequestId = Activity.Current?.Id ?? HttpContext.TraceIdentifier });
        }
    }
}
